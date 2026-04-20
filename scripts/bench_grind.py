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
import concurrent.futures
import glob
import os
import re
import shutil
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

def run_cmd(cmd: list[str], cwd: Path | str) -> tuple[int, float, str]:
    """Run a command and return (exit_code, elapsed_seconds, stdout_stderr)."""
    start = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    return proc.returncode, elapsed, proc.stdout + proc.stderr


def lake_env_lean(workspace: Path | str, lean_file: str | Path) -> tuple[int, float, str]:
    """Run a Lean file via 'lake env lean'."""
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

    Handles: "Try this: X", tagged "[apply] ..." entries, and multi-line blocks.
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

# Pattern matching `grind` as a standalone tactic word (not inside another word).
# Matches: `grind`, `grind `, `grind[`, end-of-line `grind`
GRIND_RE = re.compile(r'(?<!\w)grind(?=\s|\[|$)')


def _has_grind(line: str) -> bool:
    """Return True if line contains a grind tactic call."""
    return bool(GRIND_RE.search(line))


def _find_grind_line(source: str) -> int:
    """Return 1-indexed line number of first grind tactic, or 0 if none."""
    for i, line in enumerate(source.split("\n"), 1):
        if _has_grind(line):
            return i
    return 0


def _find_all_grind_lines(source: str) -> list[int]:
    """Return 1-indexed line numbers of all lines containing a grind tactic."""
    return [i for i, line in enumerate(source.split("\n"), 1) if _has_grind(line)]


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


def _replace_grind_on_line(line: str, replacement: str) -> str:
    """Replace the grind tactic on a single line with replacement text."""
    m = GRIND_RE.search(line)
    if not m:
        return line
    # Replace from grind to end-of-line with the first line of replacement;
    # preserve everything before grind (e.g. `use foo; `)
    before = line[:m.start()]
    return before + replacement


def _transform_grind_at_line(source: str, target_line: int, replacement: str) -> str:
    """Replace the grind tactic at target_line (1-indexed) with replacement.

    For multi-line replacements, additional lines are inserted after the target
    line, indented to the column where grind started.

    When grind follows a semicolon (e.g. ``use foo; grind``) and the
    replacement spans multiple lines, the replacement is wrapped in ``{ … }``
    so that Lean treats the whole block as a single tactic after the ``;``.
    """
    lines = source.split("\n")
    idx = target_line - 1
    line = lines[idx]
    m = GRIND_RE.search(line)
    if not m:
        return source

    before = line[:m.start()]
    grind_col = m.start()
    rep_lines = replacement.split("\n")

    # Detect whether grind follows a semicolon (possibly with whitespace).
    needs_braces = bool(re.search(r";\s*$", before)) and len(rep_lines) > 1

    if needs_braces:
        indent = " " * grind_col
        new_lines = [before + "{"]
        for rl in rep_lines:
            if rl.strip():
                new_lines.append(indent + "  " + rl)
            else:
                new_lines.append("")
        new_lines.append(indent + "}")
    else:
        new_lines = [before + rep_lines[0]]
        for rl in rep_lines[1:]:
            if rl.strip():
                new_lines.append(" " * grind_col + rl)
            else:
                new_lines.append("")

    lines[idx:idx + 1] = new_lines
    return "\n".join(lines)


def _make_query_at_line(source: str, target_line: int) -> str:
    """Replace the grind at target_line with grind? (preserving args)."""
    lines = source.split("\n")
    idx = target_line - 1
    lines[idx] = GRIND_RE.sub("grind?", lines[idx], count=1)
    return "\n".join(lines)


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


def _make_decompile_at_line(source: str, target_line: int) -> str:
    """Replace the grind at target_line with 'decompile grind', demodulify, add import."""
    lines = source.split("\n")
    idx = target_line - 1
    lines[idx] = GRIND_RE.sub("decompile grind", lines[idx], count=1)
    transformed = "\n".join(lines)
    transformed = _demodulify(transformed)
    # Insert decompile tactic import after last import line
    lines = transformed.split("\n")
    insert_at = 0
    for i, line in enumerate(lines):
        if line.strip().startswith("import "):
            insert_at = i + 1
    lines.insert(insert_at, "import LeanDecomp.ProofTermMacro")
    return "\n".join(lines)

# ---------------------------------------------------------------------------
# Treatments
# ---------------------------------------------------------------------------

@dataclass
class Treatment:
    """A benchmark treatment that transforms grind into a variant tactic."""
    name: str
    query_transform: Callable[[str, int], str]  # (source, grind_line) → query source
    out_suffix: str         # file suffix for the compiled variant
    filter: Callable[[str], bool]  # which suggestions from the query to try
    is_direct: bool = False  # if True, skip query/suggestion pipeline; use source as-is


def _identity(source: str, _grind_line: int) -> str:
    return source


def _is_grind_only(suggestion: str) -> bool:
    return suggestion.split("\n")[0].strip().startswith("grind only")


TREATMENTS = [
    Treatment("original",     _identity,
              ".original.lean",     lambda _: True, is_direct=True),
    Treatment("grindonly",   _make_query_at_line,
              ".grind_only.lean",   _is_grind_only),
    Treatment("grindscript", _make_query_at_line,
              ".grind_script.lean", lambda s: not _is_grind_only(s)),
    Treatment("decompile",    _make_decompile_at_line,
              ".decompiled.lean",   lambda _: True),
]

# ---------------------------------------------------------------------------
# Variant dataclass
# ---------------------------------------------------------------------------

@dataclass
class Variant:
    """A benchmarkable variant of a Lean file for one (treatment, grind_line) pair."""
    treatment: str
    grind_line: int
    path: Path
    suggestion: str | None
    is_direct: bool = False  # True for whole-file baseline treatments (e.g. original)


@dataclass
class DumpArtifact:
    """A generated file that should be copied to the dump directory."""
    path: Path
    dump_name: str


@dataclass
class ExtractionResult:
    """The generated outputs for one non-direct (grind_line, treatment) task."""
    variant: Variant | None
    errors: list[tuple[str, int, str]]
    dump_artifacts: list[DumpArtifact]
    generated_paths: set[Path]


# ---------------------------------------------------------------------------
# Suggestion extraction pipeline
# ---------------------------------------------------------------------------

def _get_line_suggestions(workspace: Path, source: str, grind_line: int, query_transform: Callable, suffix: str,
                          lean_file: str, treatment_name: str) -> tuple[list[str], Path, str]:
    """Run a query for one grind line. Return (suggestions, query_path, raw_output)."""
    query_source = query_transform(source, grind_line)
    query_path = Path(str(lean_file) + suffix)
    (workspace / query_path).write_text(query_source)
    print(
        f"  Running query: treatment={treatment_name}, line={grind_line}, file={query_path}",
        flush=True,
    )
    code, elapsed, combined = lake_env_lean(workspace, query_path)
    print(
        f"  Query finished: treatment={treatment_name}, line={grind_line}, "
        f"exit={code}, elapsed={elapsed:.2f}s",
        flush=True,
    )
    return extract_suggestions(combined), query_path, combined


def _try_line_suggestion(workspace: Path, source: str, grind_line: int, suggestions: list[str], lean_file: str,
                         out_suffix: str, treatment_name: str) -> tuple[str | None, Path | None, str | None]:
    """Try each suggestion for a specific grind line. Return (suggestion, path, last_error)."""
    if not suggestions:
        return None, None, None
    result_path = Path(str(lean_file) + f".L{grind_line}" + out_suffix)
    last_output = ""
    for idx, s in enumerate(suggestions, 1):
        one_line = s.replace("\n", "\\n")
        preview = one_line if len(one_line) <= 160 else one_line[:157] + "..."
        print(
            f"  Trying suggestion {idx}/{len(suggestions)}: treatment={treatment_name}, "
            f"line={grind_line}, suggestion={preview}",
            flush=True,
        )
        replaced = _transform_grind_at_line(source, grind_line, s)
        (workspace / result_path).write_text(replaced)
        code, elapsed, output = lake_env_lean(workspace, result_path)
        print(
            f"  Suggestion run finished: treatment={treatment_name}, line={grind_line}, "
            f"exit={code}, elapsed={elapsed:.2f}s",
            flush=True,
        )
        if code == 0:
            return s, result_path, None
        last_output = output
    return None, result_path, last_output.strip()


def _extract_non_direct_treatment(workspace, source, lean_file, grind_line,
                                  treatment: Treatment) -> ExtractionResult:
    """Build one non-direct treatment, including failure dump artifacts."""
    errors = []
    dump_artifacts = []
    generated_paths = set()

    suffix = f".{treatment.name}_query_L{grind_line}.lean"
    all_suggestions, qf, raw_output = _get_line_suggestions(
        workspace, source, grind_line, treatment.query_transform, suffix,
        lean_file, treatment.name)
    generated_paths.add(qf)

    filtered = [s for s in all_suggestions if treatment.filter(s)]
    if not filtered:
        dump_artifacts.append(
            DumpArtifact(qf, f"L{grind_line}.{treatment.name}.query.lean")
        )
        msg = (
            raw_output.strip()[:500] or "no output"
        ) if not all_suggestions else "no matching suggestions"
        errors.append((treatment.name, grind_line, msg))
        return ExtractionResult(None, errors, dump_artifacts, generated_paths)

    sug, sf, last_error = _try_line_suggestion(
        workspace, source, grind_line, filtered, lean_file,
        f".{treatment.name}_L{grind_line}.lean", treatment.name)
    if sf is not None:
        generated_paths.add(sf)

    if sug:
        variant = Variant(treatment.name, grind_line, sf, sug)
        dump_artifacts.append(
            DumpArtifact(qf, f"L{grind_line}.{treatment.name}.query.lean")
        )
        return ExtractionResult(variant, errors, dump_artifacts, generated_paths)

    dump_artifacts.append(
        DumpArtifact(qf, f"L{grind_line}.{treatment.name}.query.lean")
    )
    if sf is not None:
        dump_artifacts.append(
            DumpArtifact(sf, f"L{grind_line}.{treatment.name}.failed.lean")
        )

    suggestions_tried = "\n".join(f"  suggestion: {s}" for s in filtered)
    error_msg = suggestions_tried
    if last_error:
        error_msg += f"\n{last_error}"
    errors.append((treatment.name, grind_line, error_msg))
    return ExtractionResult(None, errors, dump_artifacts, generated_paths)


def _parallel_workers(task_count: int) -> int:
    """Choose a conservative worker count for subprocess-heavy tasks."""
    cpu_count = os.cpu_count() or 1
    return max(1, min(task_count, max(cpu_count - 1, 1)))


def extract_treatments(workspace, source, lean_file, grind_lines,
                       treatments=TREATMENTS):
    """For each (grind_line, treatment) pair, build generated benchmark files.

    Direct treatments (original) get one file covering the whole source unchanged.

    Returns (variants, errors, dump_artifacts, generated_paths) where:
      variants: list of Variant, one per successful (grind_line, treatment)
      errors: list of (tname, grind_line, errmsg)
      dump_artifacts: extra generated files that should be dumped on failure
      generated_paths: all temporary generated files to clean up
    """
    variants = []
    errors = []
    dump_artifacts = []
    generated_paths = set()

    # Direct treatments: one variant per grind_line (same source for each).
    for t in treatments:
        if not t.is_direct:
            continue
        for grind_line in grind_lines:
            result_path = Path(str(lean_file) + f".L{grind_line}" + t.out_suffix)
            (workspace / result_path).write_text(source)
            generated_paths.add(result_path)
            variants.append(Variant(t.name, grind_line, result_path, None, is_direct=True))

    # Non-direct: one independent task per (grind_line, treatment).
    non_direct_tasks = [
        (grind_line, t)
        for grind_line in grind_lines
        for t in treatments
        if not t.is_direct
    ]

    if non_direct_tasks:
        max_workers = _parallel_workers(len(non_direct_tasks))
        with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(
                    _extract_non_direct_treatment,
                    workspace,
                    source,
                    lean_file,
                    grind_line,
                    treatment,
                ): (grind_line, treatment.name)
                for grind_line, treatment in non_direct_tasks
            }
            try:
                for future in concurrent.futures.as_completed(futures):
                    result = future.result()
                    generated_paths.update(result.generated_paths)
                    errors.extend(result.errors)
                    dump_artifacts.extend(result.dump_artifacts)
                    if result.variant is not None:
                        variants.append(result.variant)
            except KeyboardInterrupt:
                executor.shutdown(wait=False, cancel_futures=True)
                raise
            except Exception:
                executor.shutdown(wait=False, cancel_futures=True)
                raise

    return variants, errors, dump_artifacts, generated_paths

# ---------------------------------------------------------------------------
# Benchmarking
# ---------------------------------------------------------------------------

def benchmark(workspace: Path, lean_file: Path | str, warmup: int, runs: int) -> list[float] | None:
    """Benchmark a Lean file and return a list of tactic execution times (in seconds)."""
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
    parser.add_argument(
        "--dump",
        dest="dump",
        default=None,
        help=(
            "Directory where generated benchmark Lean files should be copied. "
            "Files are written under subdirectories matching the source file path."
        ),
    )
    parser.add_argument(
        "--grind-line",
        dest="grind_lines",
        action="append",
        type=int,
        default=None,
        help=(
            "Benchmark only the specified grind line number(s). "
            "Repeat the flag to pass multiple lines."
        ),
    )
    parser.add_argument(
        "--treatment",
        dest="treatments",
        action="append",
        default=None,
        help=(
            "Treatments to run (repeatable). Choices: "
            "original, grindonly, grindscript, decompile."
        ),
    )
    parser.add_argument(
        "--no-benchmark",
        dest="no_benchmark",
        action="store_true",
        help="Skip benchmarking and only run the treatment extraction.",
    )


def _cleanup_generated_files(workspace: Path, lean_file: str) -> None:
    """Remove any generated .lean files left from previous runs."""
    pattern = str(workspace / Path(lean_file)) + ".*"
    for path in glob.glob(pattern):
        if path.endswith(".lean"):
            Path(path).unlink(missing_ok=True)


def _ensure_dump_lakefile(dump_root: Path):
    """Create a lakefile.lean in dump_root that declares lean-decomp as a dependency.
    
    Also creates symlinks to mathlib4 and lean-toolchain if they don't exist.
    """
    lakefile = dump_root / "lakefile.lean"
    dump_root.mkdir(parents=True, exist_ok=True)
    
    # Create lakefile if it doesn't exist
    if not lakefile.exists():
        content = """import Lake

open Lake DSL

package «dump» where

require "mathlib" from "./mathlib4"
require "lean-decomp" from ".."
"""
        lakefile.write_text(content)
    
    # Create symlinks to dependencies if they don't exist
    mathlib_link = dump_root / "mathlib4"
    if not mathlib_link.exists():
        mathlib_link.symlink_to("../mathlib4")
    
    toolchain_link = dump_root / "lean-toolchain"
    if not toolchain_link.exists():
        toolchain_link.symlink_to("../lean-toolchain")


def _dump_variants(workspace: Path, lean_file: str, dump_root: Path,
                   variants: list[Variant], dump_artifacts: list[DumpArtifact]):
    """Copy generated benchmark files into a stable directory for inspection."""
    source_path = Path(lean_file)
    target_dir = dump_root / source_path.parent / source_path.stem
    target_dir.mkdir(parents=True, exist_ok=True)

    for variant in variants:
        dumped_name = f"L{variant.grind_line}.{variant.treatment}.lean"
        shutil.copy2(workspace / variant.path, target_dir / dumped_name)

    for artifact in dump_artifacts:
        shutil.copy2(workspace / artifact.path, target_dir / artifact.dump_name)


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
        print(f"Not found: {workspace / lean_file}", file=sys.stderr, flush=True)
        return 2

    # Remove stale generated files from interrupted previous runs
    _cleanup_generated_files(workspace, lean_file)

    source = (workspace / lean_file).read_text()
    source = _ensure_profiler(source)
    all_grind_lines = _find_all_grind_lines(source)
    selected_lines = getattr(args, "grind_lines", None)
    if selected_lines:
        # Keep user-specified order while dropping duplicates.
        grind_lines = list(dict.fromkeys(selected_lines))
        missing = [ln for ln in grind_lines if ln not in all_grind_lines]
        if missing:
            print(
                f"Requested grind line(s) not found in {lean_file}: {missing}. "
                f"Available grind lines: {all_grind_lines}",
                file=sys.stderr,
                flush=True,
            )
            return 2
        print(
            f"  Filtering to requested grind lines for {lean_file}: {grind_lines}",
            flush=True,
        )
    else:
        grind_lines = all_grind_lines
    variants = []
    dump_artifacts = []
    generated_paths: set[Path] = set()
    dump_root = getattr(args, "dump", None)
    if dump_root is not None:
        dump_root = Path(dump_root).resolve()
        _ensure_dump_lakefile(dump_root)

    try:
        treatments = TREATMENTS
        selected = getattr(args, "treatments", None)
        if selected:
            wanted = {name.strip() for name in selected if name.strip()}
            valid = {t.name for t in TREATMENTS}
            unknown = sorted(wanted - valid)
            if unknown:
                print(
                    f"Unknown treatment(s) for {lean_file}: {unknown}. "
                    f"Valid: {sorted(valid)}",
                    file=sys.stderr,
                    flush=True,
                )
                return 2
            treatments = [t for t in TREATMENTS if t.name in wanted]

        # Extract treatment variants (includes original via identity transform)
        variants, treatment_errors, dump_artifacts, generated_paths = extract_treatments(
            workspace, source, lean_file, grind_lines, treatments=treatments)

        if dump_root is not None:
            _dump_variants(workspace, lean_file, dump_root, variants, dump_artifacts)
            print(
                f"  Dumped {len(variants) + len(dump_artifacts)} generated test file(s) for {lean_file} to {dump_root}",
                flush=True,
            )

        # Record extraction errors in the database (one row per grind call line)
        if db:
            for tname, gl, errmsg in treatment_errors:
                db.add_error(lean_file, gl, tname, errmsg)

        if getattr(args, "no_benchmark", False):
            return 0

        # Benchmark each variant — one per (grind_line, treatment).
        original_timings: dict[int, list[float]] = {}
        any_succeeded = False
        for v in variants:
            print(
                f"  Benchmarking variant: file={v.path}, line={v.grind_line}, "
                f"treatment={v.treatment}, direct={v.is_direct}",
                flush=True,
            )
            r = benchmark(workspace, v.path, args.warmup, args.runs)
            if r is None:
                print(f"  ({lean_file}:{v.grind_line}, {v.treatment}) FAILED", flush=True)
                if db:
                    db.add_error(lean_file, v.grind_line, v.treatment, "benchmark failed")
                continue
            any_succeeded = True
            mean = statistics.mean(r)
            if v.is_direct:
                original_timings[v.grind_line] = r
            if db:
                db.add_timing(lean_file, v.grind_line, v.treatment, r, applied_suggestion=v.suggestion)
            speedup_str = ""
            orig = original_timings.get(v.grind_line)
            if orig and not v.is_direct:
                orig_mean = statistics.mean(orig)
                if mean > 0:
                    speedup_str = f"  speedup: {orig_mean / mean:.3f}x"
            print(
                f"  ({lean_file}:{v.grind_line}, {v.treatment}) {mean:.4f}s{speedup_str}",
                flush=True,
            )

        # Report treatments that failed for every grind line (no variant at all).
        successful_treatments = {v.treatment for v in variants}
        for tname, gl, _ in treatment_errors:
            if tname not in successful_treatments:
                print(f"  ({lean_file}:{gl}, {tname}) FAILED", flush=True)

        if not any_succeeded:
            return 1

        return 0
    finally:
        for path in generated_paths:
            (workspace / path).unlink(missing_ok=True)
        _cleanup_generated_files(workspace, lean_file)
