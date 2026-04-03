#!/usr/bin/env python3
"""Benchmark grind search time vs expanded proof verification time.

Steps:
  1. Reads the source file (which uses `grind`)
  2. Creates a variant with `grind?` to extract suggestions
  3. Tries each suggestion, picks the first that compiles
  4. Benchmarks both the original and suggested versions
  5. Reports timing comparison
"""
import argparse
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path


def run_cmd(cmd, cwd):
    start = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    output = proc.stdout + proc.stderr
    return proc.returncode, elapsed, output


def extract_profiler_times(output: str) -> dict[str, float]:
    """Extract cumulative profiling times (in seconds) from profiler output."""
    times = {}
    in_cumulative = False
    for line in output.splitlines():
        stripped = line.strip()
        if stripped == "cumulative profiling times:":
            in_cumulative = True
            continue
        if in_cumulative:
            # Lines look like: "tactic execution 190ms" or "grind simp 29.3ms"
            m = re.match(r"(.+?)\s+([\d.]+)ms\s*$", stripped)
            if m:
                times[m.group(1).strip()] = float(m.group(2)) / 1000.0
            elif stripped:  # non-empty non-matching line ends the section
                in_cumulative = False
    return times


def extract_suggestions(output: str) -> list[str]:
    """Extract tactic suggestions from grind?/decompile output.

    Handles formats:
      - "Try this: <tactic>"                  (single-line)
      - "Try these:\\n  [tag] <tactic>\\n..."   (multi-option, each on one line)
      - "Try this:\\n  [tag]\\n    <tactic>..."  (multi-line suggestion block)
    """
    lines = output.splitlines()
    result = []

    # "Try this: <tactic>" on same line
    for line in lines:
        if "Try this: " in line:
            _, _, suggestion = line.partition("Try this: ")
            s = suggestion.strip()
            if s:
                result.append(s)

    # Multi-line block: "Try this:" or "Try these:" followed by indented content.
    # Each [tag] starts a new suggestion; subsequent indented lines continue it.
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped in ("Try this:", "Try these:"):
            i += 1
            # Collect suggestions from indented block
            while i < len(lines):
                stripped = lines[i].strip()
                if not stripped:
                    i += 1
                    continue
                # A [tag] line starts a suggestion
                m = re.match(r"\[([^\]]*)\]\s*(.*)", stripped)
                if m:
                    # Collect all lines for this suggestion until next [tag],
                    # blank non-indented line, or end of block
                    tag_indent = len(lines[i]) - len(lines[i].lstrip())
                    parts = []
                    rest = m.group(2).rstrip()
                    # Find the indentation of the first content line
                    content_indent = None
                    if rest:
                        parts.append(rest)
                    i += 1
                    while i < len(lines):
                        raw = lines[i]
                        line_stripped = raw.strip()
                        cur_indent = len(raw) - len(raw.lstrip())
                        # Stop at next [tag] at same indent, or unindented non-empty line
                        if line_stripped and cur_indent <= tag_indent:
                            break
                        if line_stripped:
                            if content_indent is None:
                                content_indent = cur_indent
                            # Preserve indentation relative to first content line
                            rel = max(cur_indent - content_indent, 0)
                            parts.append(" " * rel + line_stripped)
                        i += 1
                    suggestion = "\n".join(parts).strip()
                    if suggestion:
                        result.append(suggestion)
                else:
                    # Not a [tag] line — if it's indented, it's a continuation of
                    # a single suggestion (Try this:\n  tactic)
                    cur_indent = len(lines[i]) - len(lines[i].lstrip())
                    if cur_indent > 0:
                        parts = [stripped]
                        base_indent = cur_indent
                        i += 1
                        while i < len(lines):
                            raw = lines[i]
                            line_stripped = raw.strip()
                            ci = len(raw) - len(raw.lstrip())
                            if line_stripped and ci < base_indent:
                                break
                            if line_stripped:
                                rel = max(ci - base_indent, 0)
                                parts.append(" " * rel + line_stripped)
                            i += 1
                        suggestion = "\n".join(parts).strip()
                        if suggestion:
                            result.append(suggestion)
                    else:
                        break  # end of suggestion block
        else:
            i += 1

    return result


def get_indent(line: str) -> str:
    return line[: len(line) - len(line.lstrip())]


def is_grind_line(trimmed: str) -> bool:
    return trimmed.startswith("grind ") or trimmed.startswith("grind[") or trimmed == "grind"


def make_query_source(source: str) -> str:
    """Replace `grind ...` with `grind? ...`."""
    lines = []
    for line in source.split("\n"):
        trimmed = line.lstrip()
        if is_grind_line(trimmed):
            lines.append(get_indent(line) + "grind?" + trimmed[5:])
        else:
            lines.append(line)
    return "\n".join(lines)


def make_decompile_source(source: str) -> str:
    """Replace `grind ...` with `decompile grind ...`."""
    lines = []
    for line in source.split("\n"):
        trimmed = line.lstrip()
        if is_grind_line(trimmed):
            lines.append(get_indent(line) + "decompile " + trimmed)
        else:
            lines.append(line)
    return "\n".join(lines)


def apply_replacement(source: str, suggestion: str) -> str:
    """Replace `grind ...` lines with the given suggestion (possibly multi-line)."""
    lines = []
    for line in source.split("\n"):
        trimmed = line.lstrip()
        if is_grind_line(trimmed):
            indent = get_indent(line)
            sug_lines = suggestion.split("\n")
            lines.append(indent + sug_lines[0])
            for sl in sug_lines[1:]:
                lines.append(indent + sl if sl.strip() else sl)
        else:
            lines.append(line)
    return "\n".join(lines)


def format_stats(samples):
    return {
        "count": len(samples),
        "mean": statistics.mean(samples),
        "median": statistics.median(samples),
        "stdev": statistics.stdev(samples) if len(samples) > 1 else 0.0,
        "min": min(samples),
        "max": max(samples),
    }


def benchmark(cmd, cwd, warmup, runs, label=""):
    for i in range(warmup):
        code, elapsed, output = run_cmd(cmd, cwd)
        print(f"  warmup {i + 1}/{warmup}: {elapsed:.3f}s (exit={code})")
        if code != 0:
            print(output)
            return None, None

    wall_samples = []
    tactic_samples = []
    for i in range(runs):
        code, elapsed, output = run_cmd(cmd, cwd)
        ptimes = extract_profiler_times(output)
        tactic_ms = ptimes.get("tactic execution")
        tactic_str = f", tactic={tactic_ms:.4f}s" if tactic_ms is not None else ""
        print(f"  run {i + 1}/{runs}: {elapsed:.3f}s{tactic_str} (exit={code})")
        if code != 0:
            print(output)
            return None, None
        wall_samples.append(elapsed)
        if tactic_ms is not None:
            tactic_samples.append(tactic_ms)
    return wall_samples, tactic_samples if tactic_samples else None


def main():
    parser = argparse.ArgumentParser(
        description="Benchmark grind search time vs expanded proof verification time."
    )
    parser.add_argument("--runs", type=int, default=10, help="Number of measured runs (default: 10)")
    parser.add_argument("--warmup", type=int, default=2, help="Warmup runs before measurement (default: 2)")
    parser.add_argument(
        "--workspace",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Path to workspace root (default: repo root)",
    )
    parser.add_argument(
        "--lean-file",
        default="LeanDecomp/BenchGrind.lean",
        help="Lean file to run (default: LeanDecomp/BenchGrind.lean)",
    )
    parser.add_argument(
        "--theorem",
        default="bench_if_true",
        help="Theorem name to look for in profiler output (default: bench_if_true)",
    )
    args = parser.parse_args()

    if args.runs <= 0:
        print("--runs must be > 0", file=sys.stderr)
        return 2

    workspace = args.workspace.resolve()
    if not workspace.exists():
        print(f"Workspace does not exist: {workspace}", file=sys.stderr)
        return 2

    lean_file = workspace / args.lean_file
    if not lean_file.exists():
        print(f"Lean file not found: {lean_file}", file=sys.stderr)
        return 2

    source = lean_file.read_text()

    # Build dependencies
    print("Preparing with: lake build")
    code, elapsed, output = run_cmd(["lake", "build"], workspace)
    print(f"  prepare exit={code} time={elapsed:.3f}s")
    if code != 0:
        print(output)
        return code

    # Create grind? variant and extract suggestions
    query_source = make_query_source(source)
    query_file = Path(args.lean_file + ".query.lean")
    (workspace / query_file).write_text(query_source)

    print("Running grind? variant...")
    code, _, combined = run_cmd(["lake", "env", "lean", str(query_file)], workspace)
    suggestions = extract_suggestions(combined)

    if not suggestions:
        print(f"No suggestions found.\nOutput:\n{combined}", file=sys.stderr)
        (workspace / query_file).unlink(missing_ok=True)
        return 1

    print(f"  Found {len(suggestions)} suggestion(s):")
    for s in suggestions:
        print(f"    {s}")

    # Try each suggestion, use the first that compiles
    sug_file = Path(args.lean_file + ".suggested.lean")
    working = None
    for s in suggestions:
        print(f"  Trying: {s}")
        (workspace / sug_file).write_text(apply_replacement(source, s))
        code, _, _ = run_cmd(["lake", "env", "lean", str(sug_file)], workspace)
        if code == 0:
            print(f"    ok")
            working = s
            break
        else:
            print(f"    failed")

    if working is None:
        print("No suggestion compiled successfully!", file=sys.stderr)
        (workspace / query_file).unlink(missing_ok=True)
        (workspace / sug_file).unlink(missing_ok=True)
        return 1

    print(f"  Using: {working}")
    (workspace / sug_file).write_text(apply_replacement(source, working))

    # Create decompile variant and extract suggestion
    decomp_query_source = make_decompile_source(source)
    decomp_query_file = Path(args.lean_file + ".decomp_query.lean")
    (workspace / decomp_query_file).write_text(decomp_query_source)

    print("Running decompile variant...")
    code, _, decomp_combined = run_cmd(["lake", "env", "lean", str(decomp_query_file)], workspace)
    decomp_suggestions = extract_suggestions(decomp_combined)

    decomp_working = None
    decomp_file = Path(args.lean_file + ".decompiled.lean")
    if not decomp_suggestions:
        print(f"  No decompile suggestions found (will skip decompile benchmark).")
    else:
        print(f"  Found {len(decomp_suggestions)} decompile suggestion(s):")
        for s in decomp_suggestions:
            print(f"    {s}")

        for s in decomp_suggestions:
            print(f"  Trying: {s}")
            (workspace / decomp_file).write_text(apply_replacement(source, s))
            code, _, _ = run_cmd(["lake", "env", "lean", str(decomp_file)], workspace)
            if code == 0:
                print(f"    ok")
                decomp_working = s
                break
            else:
                print(f"    failed")

        if decomp_working:
            print(f"  Using: {decomp_working}")
            (workspace / decomp_file).write_text(apply_replacement(source, decomp_working))
        else:
            print("  No decompile suggestion compiled (will skip decompile benchmark).")

    # Benchmark original
    cmd_orig = ["lake", "env", "lean", args.lean_file]
    cmd_sug = ["lake", "env", "lean", str(sug_file)]

    print(f"\n── Original (grind search) ──")
    orig_wall, orig_tactic = benchmark(cmd_orig, workspace, args.warmup, args.runs)
    if orig_wall is None:
        return 1

    print(f"\n── grind? suggestion ──")
    sug_wall, sug_tactic = benchmark(cmd_sug, workspace, args.warmup, args.runs)
    if sug_wall is None:
        return 1

    decomp_wall = decomp_tactic = None
    if decomp_working:
        cmd_decomp = ["lake", "env", "lean", str(decomp_file)]
        print(f"\n── decompile suggestion ──")
        decomp_wall, decomp_tactic = benchmark(cmd_decomp, workspace, args.warmup, args.runs)
        if decomp_wall is None:
            return 1

    # Report
    all_results = [
        ("Original", orig_wall, orig_tactic),
        ("grind?", sug_wall, sug_tactic),
    ]
    if decomp_wall:
        all_results.append(("decompile", decomp_wall, decomp_tactic))

    print("\n── Summary ──")
    for label, wall, tactic in all_results:
        stats = format_stats(wall)
        print(f"  {label} (wall-clock):")
        print(f"    mean:   {stats['mean']:.4f}s")
        print(f"    median: {stats['median']:.4f}s")
        print(f"    stdev:  {stats['stdev']:.4f}s")
        print(f"    min:    {stats['min']:.4f}s")
        print(f"    max:    {stats['max']:.4f}s")
        if tactic:
            ts = format_stats(tactic)
            print(f"  {label} (profiler tactic execution):")
            print(f"    mean:   {ts['mean']:.4f}s")
            print(f"    median: {ts['median']:.4f}s")
            print(f"    stdev:  {ts['stdev']:.4f}s")
            print(f"    min:    {ts['min']:.4f}s")
            print(f"    max:    {ts['max']:.4f}s")

    # Speedup comparisons using profiler times when available, wall-clock otherwise
    def get_mean(wall, tactic):
        return statistics.mean(tactic) if tactic else statistics.mean(wall)

    def timing_label(tactic):
        return "profiler" if tactic else "wall-clock"

    orig_mean = get_mean(orig_wall, orig_tactic)
    sug_mean = get_mean(sug_wall, sug_tactic)
    kind = timing_label(orig_tactic)
    if sug_mean > 0:
        print(f"\n  grind? speedup over original: {orig_mean / sug_mean:.3f}x ({kind})")
    if decomp_wall:
        decomp_mean = get_mean(decomp_wall, decomp_tactic)
        if decomp_mean > 0:
            print(f"  decompile speedup over original: {orig_mean / decomp_mean:.3f}x ({kind})")
            print(f"  decompile speedup over grind?: {sug_mean / decomp_mean:.3f}x ({kind})")


    # Cleanup
    (workspace / query_file).unlink(missing_ok=True)
    (workspace / sug_file).unlink(missing_ok=True)
    (workspace / decomp_query_file).unlink(missing_ok=True)
    (workspace / decomp_file).unlink(missing_ok=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
