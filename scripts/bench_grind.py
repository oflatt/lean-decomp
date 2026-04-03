#!/usr/bin/env python3
"""Benchmark grind variants: original, grind only, grind script, decompile.

Reads a Lean file containing `grind`, generates variants with `grind?` and
`decompile grind`, splits grind? suggestions into 'grind only [...]' (lemma
restrictions) and 'grind script' (tactic scripts with =>), and benchmarks
each using Lean's built-in profiler for tactic-level timing.

NOTE: The output parsing (profiler format, suggestion format) is sensitive to
the Lean version. This script was developed against the toolchain specified in
lean-toolchain (v4.28.0-rc1 at time of writing) and may need updates for other
versions.
"""
import argparse
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# Subprocess helpers
# ---------------------------------------------------------------------------

def run_cmd(cmd, cwd):
    start = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    return proc.returncode, elapsed, proc.stdout + proc.stderr


def lake_env_lean(workspace, lean_file):
    return run_cmd(["lake", "env", "lean", str(lean_file)], workspace)

# ---------------------------------------------------------------------------
# Output parsing
# ---------------------------------------------------------------------------

def extract_profiler_times(output: str) -> dict[str, float]:
    """Extract cumulative profiling times (in seconds) from profiler output."""
    times = {}
    in_section = False
    for line in output.splitlines():
        stripped = line.strip()
        if stripped == "cumulative profiling times:":
            in_section = True
        elif in_section:
            m = re.match(r"(.+?)\s+([\d.]+)ms\s*$", stripped)
            if m:
                times[m.group(1).strip()] = float(m.group(2)) / 1000.0
            elif stripped:
                in_section = False
    return times


def extract_suggestions(output: str) -> list[str]:
    """Extract tactic suggestions from grind?/decompile output.

    Handles: "Try this: X", "Try these:\\n [tag] X", and multi-line blocks.
    """
    lines = output.splitlines()
    result = []

    # Single-line: "Try this: <tactic>"
    for line in lines:
        if "Try this: " in line:
            s = line.partition("Try this: ")[2].strip()
            if s:
                result.append(s)

    # Multi-line block after "Try this:" or "Try these:"
    i = 0
    while i < len(lines):
        if lines[i].strip() in ("Try this:", "Try these:"):
            i += 1
            while i < len(lines):
                stripped = lines[i].strip()
                if not stripped:
                    i += 1
                    continue
                m = re.match(r"\[[^\]]*\]\s*(.*)", stripped)
                if m:
                    result.append(_collect_indented_block(lines, i, m.group(1).rstrip()))
                    i = _skip_indented(lines, i)
                elif len(lines[i]) > len(lines[i].lstrip()):
                    result.append(_collect_indented_block(lines, i))
                    i = _skip_indented(lines, i)
                else:
                    break
        else:
            i += 1

    return [s for s in result if s]


def _collect_indented_block(lines, start, first_part=""):
    """Collect a multi-line suggestion preserving relative indentation."""
    tag_indent = len(lines[start]) - len(lines[start].lstrip())
    parts = [first_part] if first_part else []
    base_indent = None
    i = start + 1
    while i < len(lines):
        raw = lines[i]
        stripped = raw.strip()
        indent = len(raw) - len(raw.lstrip())
        if stripped and indent <= tag_indent:
            break
        if stripped:
            if base_indent is None:
                base_indent = indent
            parts.append(" " * max(indent - base_indent, 0) + stripped)
        i += 1
    return "\n".join(parts).strip()


def _skip_indented(lines, start):
    """Return index past the indented block starting at `start`."""
    tag_indent = len(lines[start]) - len(lines[start].lstrip())
    i = start + 1
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped and len(lines[i]) - len(lines[i].lstrip()) <= tag_indent:
            break
        i += 1
    return i

# ---------------------------------------------------------------------------
# Source transformation
# ---------------------------------------------------------------------------

def _is_grind_line(trimmed: str) -> bool:
    return trimmed.startswith("grind ") or trimmed.startswith("grind[") or trimmed == "grind"


def _transform_grind_lines(source: str, fn) -> str:
    """Apply `fn(indent, trimmed)` to each grind line, keep others unchanged."""
    out = []
    for line in source.split("\n"):
        trimmed = line.lstrip()
        if _is_grind_line(trimmed):
            indent = line[: len(line) - len(trimmed)]
            out.append(fn(indent, trimmed))
        else:
            out.append(line)
    return "\n".join(out)


def make_query_source(source):
    return _transform_grind_lines(source, lambda ind, t: ind + "grind?" + t[5:])


def make_decompile_source(source):
    return _transform_grind_lines(source, lambda ind, t: ind + "decompile " + t)


def apply_replacement(source, suggestion):
    def replace(indent, _trimmed):
        sug_lines = suggestion.split("\n")
        return "\n".join(
            (indent + sl if i == 0 or sl.strip() else sl)
            for i, sl in enumerate(sug_lines)
        )
    return _transform_grind_lines(source, replace)

# ---------------------------------------------------------------------------
# Suggestion extraction pipeline
# ---------------------------------------------------------------------------

def get_suggestions(workspace, variant_source, suffix, lean_file):
    """Write variant source, run it, return (suggestions, query_path)."""
    query_path = Path(lean_file + suffix)
    (workspace / query_path).write_text(variant_source)
    _, _, combined = lake_env_lean(workspace, query_path)
    return extract_suggestions(combined), query_path


def try_suggestions(workspace, source, suggestions, lean_file, out_suffix):
    """Try each suggestion until one compiles. Return (suggestion, file) or (None, None)."""
    if not suggestions:
        return None, None
    result_path = Path(lean_file + out_suffix)
    for s in suggestions:
        (workspace / result_path).write_text(apply_replacement(source, s))
        code, _, _ = lake_env_lean(workspace, result_path)
        if code == 0:
            print(f"  Using: {s.split(chr(10))[0]}{'...' if chr(10) in s else ''}")
            return s, result_path
        print(f"  Tried and failed: {s.split(chr(10))[0]}")
    (workspace / result_path).unlink(missing_ok=True)
    return None, None


def is_grind_only(suggestion: str) -> bool:
    """True if the suggestion is a `grind only [...]` style (not a tactic script)."""
    first_line = suggestion.split("\n")[0].strip()
    return first_line.startswith("grind only")

# ---------------------------------------------------------------------------
# Benchmarking
# ---------------------------------------------------------------------------

def benchmark(workspace, lean_file, warmup, runs):
    cmd = ["lake", "env", "lean", str(lean_file)]
    for i in range(warmup):
        code, _, _ = run_cmd(cmd, workspace)
        print(f"  warmup {i+1}/{warmup}")
        if code != 0:
            return None

    samples = []
    for i in range(runs):
        code, _, output = run_cmd(cmd, workspace)
        ptimes = extract_profiler_times(output)
        t = ptimes.get("tactic execution")
        if t is None:
            print(f"  run {i+1}/{runs}: no profiler output")
        else:
            print(f"  run {i+1}/{runs}: {t:.4f}s")
            samples.append(t)
        if code != 0:
            return None
    return samples or None


def print_stats(label, samples):
    mean = statistics.mean(samples)
    median = statistics.median(samples)
    stdev = statistics.stdev(samples) if len(samples) > 1 else 0.0
    print(f"  {label}:  mean={mean:.4f}s  median={median:.4f}s  "
          f"stdev={stdev:.4f}s  min={min(samples):.4f}s  max={max(samples):.4f}s")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Benchmark grind vs grind? suggestion vs decompile suggestion."
    )
    parser.add_argument("--runs", type=int, default=10)
    parser.add_argument("--warmup", type=int, default=2)
    parser.add_argument("--workspace", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lean-file", default="LeanDecomp/BenchGrind.lean")
    args = parser.parse_args()

    workspace = args.workspace.resolve()
    lean_file = args.lean_file
    if not (workspace / lean_file).exists():
        print(f"Not found: {workspace / lean_file}", file=sys.stderr)
        return 2

    source = (workspace / lean_file).read_text()
    temp_files = []

    # Build dependencies
    print("Building dependencies...")
    code, _, output = run_cmd(["lake", "build"], workspace)
    if code != 0:
        print(output, file=sys.stderr)
        return 1

    # Extract suggestions for each variant
    variants = [("original", lean_file, None)]

    print("\nExtracting grind? suggestions...")
    grind_suggestions, qf = get_suggestions(
        workspace, make_query_source(source), ".query.lean", lean_file)
    temp_files.append(qf)
    if grind_suggestions:
        print(f"  Found {len(grind_suggestions)} suggestion(s):")
        for s in grind_suggestions:
            first_line = s.split("\n")[0]
            ellipsis = " ..." if "\n" in s else ""
            print(f"    {first_line}{ellipsis}")

        only_sugs = [s for s in grind_suggestions if is_grind_only(s)]
        script_sugs = [s for s in grind_suggestions if not is_grind_only(s)]

        if only_sugs:
            print(f"\n  Trying {len(only_sugs)} 'grind only' suggestion(s)...")
            sug, sf = try_suggestions(
                workspace, source, only_sugs, lean_file, ".grind_only.lean")
            if sug:
                variants.append(("grind only", str(sf), sug))
                temp_files.append(sf)

        if script_sugs:
            print(f"\n  Trying {len(script_sugs)} 'grind script' suggestion(s)...")
            sug, sf = try_suggestions(
                workspace, source, script_sugs, lean_file, ".grind_script.lean")
            if sug:
                variants.append(("grind script", str(sf), sug))
                temp_files.append(sf)
    else:
        print("  No suggestions found.")

    print("\nExtracting decompile suggestion...")
    decomp_suggestions, qf = get_suggestions(
        workspace, make_decompile_source(source), ".decomp_query.lean", lean_file)
    temp_files.append(qf)
    if decomp_suggestions:
        print(f"  Found {len(decomp_suggestions)} suggestion(s):")
        for s in decomp_suggestions:
            first_line = s.split("\n")[0]
            ellipsis = " ..." if "\n" in s else ""
            print(f"    {first_line}{ellipsis}")
        sug, sf = try_suggestions(
            workspace, source, decomp_suggestions, lean_file, ".decompiled.lean")
        if sug:
            variants.append(("decompile", str(sf), sug))
            temp_files.append(sf)
    else:
        print("  No suggestions found.")

    # Show what each variant uses
    print("\n── Variants ──")
    # Find the original grind tactic from source
    orig_tactic = None
    for line in source.split("\n"):
        trimmed = line.lstrip()
        if _is_grind_line(trimmed):
            orig_tactic = trimmed
            break
    for label, file, suggestion in variants:
        tactic = suggestion if suggestion else orig_tactic
        print(f"\n  {label}:")
        if tactic:
            for tl in tactic.split("\n"):
                print(f"    {tl}")
        print(f"    file: {file}")

    # Benchmark each variant
    results = {}
    for label, file, _ in variants:
        print(f"\n── {label} ──")
        r = benchmark(workspace, file, args.warmup, args.runs)
        if r is None:
            return 1
        results[label] = r

    # Report
    print("\n── Summary (tactic execution time) ──")
    for label, _, _ in variants:
        print_stats(label, results[label])

    orig = statistics.mean(results["original"])
    for label, _, _ in variants[1:]:
        m = statistics.mean(results[label])
        if m > 0:
            print(f"  {label} speedup: {orig / m:.3f}x")

    # Cleanup
    for f in temp_files:
        (workspace / f).unlink(missing_ok=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
