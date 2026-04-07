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
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from bench_db import BenchDB

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


def _find_grind_line(source: str) -> int:
    """Return 1-indexed line number of first grind tactic, or 0 if none."""
    for i, line in enumerate(source.split("\n"), 1):
        if _is_grind_line(line.lstrip()):
            return i
    return 0


def _ensure_profiler(source: str) -> str:
    """Inject `set_option profiler true`."""
    # Insert after the last import/module block line
    lines = source.split("\n")
    insert_at = 0
    for i, line in enumerate(lines):
        stripped = line.strip()
        if (stripped.startswith("import ")
            or stripped.startswith("public import ")
            or stripped == "module"):
            insert_at = i + 1
    lines.insert(insert_at, "set_option profiler true")
    return "\n".join(lines)


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


def _demodulify(source: str) -> str:
    """Strip `module` keyword and convert module-only import forms to plain `import`.

    Handles `public import`, `meta import`, and `public meta import`.
    Needed so we can add a regular (non-module) import to a module file.
    Only affects the generated query file, not the original source.
    """
    lines = source.split("\n")
    out = []
    for line in lines:
        stripped = line.strip()
        if stripped == "module":
            continue
        new = line.replace("public ", "", 1) if stripped.startswith("public ") else line
        new_stripped = new.strip()
        new = new.replace("meta import", "import", 1) if new_stripped.startswith("meta import") else new
        out.append(new)
    return "\n".join(out)


def make_decompile_source(source):
    transformed = _transform_grind_lines(source, lambda ind, t: ind + "decompile " + t)
    transformed = _demodulify(transformed)
    # Insert decompile tactic import after last import line
    lines = transformed.split("\n")
    insert_at = 0
    for i, line in enumerate(lines):
        if line.strip().startswith("import "):
            insert_at = i + 1
    lines.insert(insert_at, "import LeanDecomp.ProofTermMacro")
    return "\n".join(lines)


def apply_replacement(source, suggestion):
    def replace(indent, _trimmed):
        sug_lines = suggestion.split("\n")
        return "\n".join(
            (indent + sl if i == 0 or sl.strip() else sl)
            for i, sl in enumerate(sug_lines)
        )
    return _transform_grind_lines(source, replace)

# ---------------------------------------------------------------------------
# Treatments
# ---------------------------------------------------------------------------

@dataclass
class Treatment:
    """A benchmark treatment that transforms grind into a variant tactic."""
    name: str
    query_transform: Callable[[str], str]  # source → query source
    out_suffix: str         # file suffix for the compiled variant
    filter: Callable[[str], bool]  # which suggestions from the query to try


def _is_grind_only(suggestion: str) -> bool:
    return suggestion.split("\n")[0].strip().startswith("grind only")


TREATMENTS = [
    Treatment("grindonly",   make_query_source,
              ".grind_only.lean",   _is_grind_only),
    Treatment("grindscript", make_query_source,
              ".grind_script.lean", lambda s: not _is_grind_only(s)),
    Treatment("decompile",    make_decompile_source,
              ".decompiled.lean",   lambda _: True),
]

# ---------------------------------------------------------------------------
# Suggestion extraction pipeline
# ---------------------------------------------------------------------------

def _get_suggestions(workspace, variant_source, suffix, lean_file):
    """Write variant source, run it, return (suggestions, query_path, raw_output)."""
    query_path = Path(lean_file + suffix)
    (workspace / query_path).write_text(variant_source)
    _, _, combined = lake_env_lean(workspace, query_path)
    return extract_suggestions(combined), query_path, combined


def _try_suggestions(workspace, source, suggestions, lean_file, out_suffix):
    """Try each suggestion until one compiles. Return (suggestion, file, last_error)."""
    if not suggestions:
        return None, None, None
    result_path = Path(lean_file + out_suffix)
    last_output = ""
    for s in suggestions:
        (workspace / result_path).write_text(apply_replacement(source, s))
        code, _, output = lake_env_lean(workspace, result_path)
        if code == 0:
            return s, result_path, None
        last_output = output
    (workspace / result_path).unlink(missing_ok=True)
    return None, None, last_output.strip()


def extract_treatments(workspace, source, lean_file, treatments=TREATMENTS):
    """Run queries and extract working suggestions for each treatment.

    Returns (variants, temp_files, errors) where variants is a list of
    (label, file_path_str, suggestion_or_None) and errors is a list of
    (treatment_name, error_message).
    """
    temp_files = []
    variants = []
    errors = []

    for t in treatments:
        query_suffix = f".{t.name}_query.lean"
        all_suggestions, qf, raw_output = _get_suggestions(
            workspace, t.query_transform(source), query_suffix, lean_file)
        temp_files.append(qf)

        if not all_suggestions:
            errors.append((t.name, raw_output.strip() or "no output"))
            continue

        filtered = [s for s in all_suggestions if t.filter(s)]
        if not filtered:
            errors.append((t.name, "no matching suggestions"))
            continue

        sug, sf, last_error = _try_suggestions(
            workspace, source, filtered, lean_file, t.out_suffix)
        if sug:
            variants.append((t.name, str(sf), sug))
            temp_files.append(sf)
        else:
            suggestions_tried = "\n".join(f"suggestion: {s}" for s in filtered)
            error_msg = f"{suggestions_tried}\n{last_error}" if last_error else suggestions_tried
            errors.append((t.name, error_msg))

    return variants, temp_files, errors

# ---------------------------------------------------------------------------
# Benchmarking
# ---------------------------------------------------------------------------

def benchmark(workspace, lean_file, warmup, runs):
    cmd = ["lake", "env", "lean", str(lean_file)]
    for i in range(warmup):
        code, _, _ = run_cmd(cmd, workspace)
        if code != 0:
            return None

    samples = []
    for i in range(runs):
        code, _, output = run_cmd(cmd, workspace)
        ptimes = extract_profiler_times(output)
        t = ptimes.get("tactic execution")
        if t is not None:
            samples.append(t)
        if code != 0:
            return None
    return samples or None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def add_bench_args(parser: argparse.ArgumentParser):
    """Add bench_grind arguments to a parser."""
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--warmup", type=int, default=1)


def bench_grind(lean_file: str, workspace: Path, args: argparse.Namespace,
                db: BenchDB | None = None):
    """Benchmark grind variants for a single Lean file.

    Args:
        lean_file: Lean file to benchmark (relative to workspace).
        workspace: Root workspace directory (where `lake` runs).
        args: Parsed arguments with runs, warmup fields.
        db: Optional results database to populate.

    Returns:
        0 on success, non-zero on failure.
    """
    workspace = workspace.resolve()
    if not (workspace / lean_file).exists():
        print(f"Not found: {workspace / lean_file}", file=sys.stderr)
        return 2

    source = (workspace / lean_file).read_text()
    source = _ensure_profiler(source)
    grind_line = _find_grind_line(source)
    temp_files = []

    # Write profiler-enabled original as a temp file for benchmarking
    orig_path = Path(lean_file + ".original.lean")
    (workspace / orig_path).write_text(source)
    temp_files.append(orig_path)

    # Extract treatment variants
    variants = [("original", str(orig_path), None)]
    treatment_variants, treatment_temps, treatment_errors = extract_treatments(
        workspace, source, lean_file)
    variants.extend(treatment_variants)
    temp_files.extend(treatment_temps)

    # Record extraction errors in the database
    if db:
        for tname, errmsg in treatment_errors:
            db.add_error(lean_file, grind_line, tname, errmsg)

    # Benchmark each variant
    results = {}
    for label, file, _ in variants:
        r = benchmark(workspace, file, args.warmup, args.runs)
        if r is None:
            print(f"  ({lean_file}:{grind_line}, {label}) FAILED")
            if db:
                db.add_error(lean_file, grind_line, label, "benchmark failed")
            continue
        results[label] = r
        if db:
            db.add_timing(lean_file, grind_line, label, r)
        mean = statistics.mean(r)
        print(f"  ({lean_file}:{grind_line}, {label}) {mean:.4f}s")

    # Print extraction errors briefly
    for tname, _ in treatment_errors:
        print(f"  ({lean_file}:{grind_line}, {tname}) FAILED")

    if not results:
        # Cleanup
        for f in temp_files:
            (workspace / f).unlink(missing_ok=True)
        return 1

    # Speedup summary
    if "original" in results:
        orig = statistics.mean(results["original"])
        for label, _, _ in variants[1:]:
            if label in results:
                m = statistics.mean(results[label])
                if m > 0:
                    print(f"  ({lean_file}:{grind_line}, {label}) speedup: {orig / m:.3f}x")

    # Cleanup
    for f in temp_files:
        (workspace / f).unlink(missing_ok=True)
    return 0
