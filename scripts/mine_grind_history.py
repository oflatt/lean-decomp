#!/usr/bin/env python3
"""Mine recent mathlib history for removed `grind` tactic calls.

The script scans git history for Lean-file diffs that delete lines containing a
standalone `grind` tactic call, then records the replacement lines from the same
hunk. This is useful for finding places where `grind` was removed in favor of a
more manual proof, which may indicate historically expensive or brittle uses.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from collections import Counter
from dataclasses import asdict, dataclass
from datetime import date, timedelta
from pathlib import Path
from typing import Iterable

from bench_grind import extract_profiler_times

COMMIT_MARKER = "__GRIND_HISTORY_COMMIT__"
DIFF_MARKER = "diff --git "
LEAN_PATHSPEC = ":(glob)**/*.lean"
GRIND_RE = re.compile(r"(?<![A-Za-z0-9_])grind(?=\s|\[|$|[;,)])")
TACTIC_PATTERNS = (
    re.compile(r"(^|\s)grind(?=\s|\[|$|[;,)])"),
    re.compile(r"\bby\s+grind(?=\s|\[|$|[;,)])"),
    re.compile(r";\s*grind(?=\s|\[|$|[;,)])"),
    re.compile(r"<;>\s*grind(?=\s|\[|$|[;,)])"),
    re.compile(r"=>\s*grind(?=\s|\[|$|[;,)])"),
    re.compile(r"\bwith\s+grind(?=\s|\[|$|[;,)])"),
)
COMMENT_PREFIXES = ("--", "/-", "*", "#adaptation_note")
AUTOMATION_KEYWORDS = (
    "grind",
    "simp",
    "simpa",
    "omega",
    "linarith",
    "nlinarith",
    "positivity",
    "aesop",
    "tauto",
    "decide",
    "native_decide",
    "ring",
    "norm_num",
    "abel",
    "canon",
    "canonicalizer",
)


@dataclass
class CommitInfo:
    commit: str
    date: str
    subject: str


@dataclass
class HunkRecord:
    commit: str
    date: str
    subject: str
    before_file: str
    file: str
    hunk: str
    grind_line: int
    removed_lines: list[str]
    added_lines: list[str]
    classification: str
    timing: "TimingResult | None" = None


@dataclass
class TimingResult:
    status: str
    before_rev: str
    after_rev: str
    warmup: int
    runs: int
    wall_before: list[float]
    wall_after: list[float]
    tactic_before: list[float] | None
    tactic_after: list[float] | None
    wall_mean_before: float | None
    wall_mean_after: float | None
    wall_delta: float | None
    wall_speedup: float | None
    tactic_mean_before: float | None
    tactic_mean_after: float | None
    tactic_delta: float | None
    tactic_speedup: float | None
    error: str | None = None


@dataclass
class Report:
    repo: str
    since: str
    until: str | None
    commits_with_grind_diffs: int
    removal_count: int
    classification_counts: dict[str, int]
    removals: list[HunkRecord]


def run_git(repo: Path, args: list[str]) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return proc.stdout


def run_cmd(cmd: list[str], cwd: Path) -> tuple[int, float, str]:
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    elapsed = time.perf_counter() - t0
    return proc.returncode, elapsed, proc.stdout + proc.stderr


def _ensure_profiler(source: str) -> str:
    """Inject `set_option profiler true` near the import block."""
    lines = source.split("\n")
    insert_at = 0
    for i, line in enumerate(lines):
        stripped = line.strip()
        if (
            stripped.startswith("prelude")
            or stripped.startswith("import ")
            or stripped.startswith("public import ")
            or stripped == "module"
        ):
            insert_at = i + 1
    lines.insert(insert_at, "set_option profiler true")
    return "\n".join(lines)


def _resolve_rev(repo: Path, rev: str) -> str:
    return run_git(repo, ["rev-parse", rev]).strip()


def _add_worktree(repo: Path, dest: Path, rev: str) -> None:
    proc = subprocess.run(
        ["git", "-C", str(repo), "worktree", "add", "--detach", str(dest), rev],
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or f"git worktree add failed for {rev}")


def _remove_worktree(repo: Path, dest: Path) -> None:
    subprocess.run(
        ["git", "-C", str(repo), "worktree", "remove", "--force", str(dest)],
        check=False,
        capture_output=True,
        text=True,
    )
    shutil.rmtree(dest, ignore_errors=True)


def _maybe_fetch_cache(worktree: Path) -> str | None:
    proc = subprocess.run(
        ["lake", "exe", "cache", "get"],
        cwd=worktree,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        message = (proc.stdout + proc.stderr).strip()
        return message or "lake exe cache get failed"
    return None


def _module_name(lean_file: str) -> str:
    if not lean_file.endswith(".lean"):
        raise RuntimeError(f"not a Lean file: {lean_file}")
    return lean_file.removesuffix(".lean").replace("/", ".")


def _clear_module_build_outputs(worktree: Path, lean_file: str) -> None:
    rel = Path(lean_file).with_suffix("")
    build_root = worktree / ".lake" / "build" / "lib"
    for ext in (".olean", ".ilean", ".c", ".trace", ".hash"):
        (build_root / rel).with_suffix(ext).unlink(missing_ok=True)


def _benchmark_file(worktree: Path, lean_file: str, warmup: int, runs: int) -> tuple[list[float], list[float] | None]:
    source_path = worktree / lean_file
    if not source_path.exists():
        raise RuntimeError(f"file not found at revision: {lean_file}")
    module_name = _module_name(lean_file)
    original_source = source_path.read_text()
    source_path.write_text(_ensure_profiler(original_source))

    try:
        for _ in range(warmup):
            _clear_module_build_outputs(worktree, lean_file)
            code, _, output = run_cmd(["lake", "build", module_name], worktree)
            if code != 0:
                raise RuntimeError(output.strip() or "benchmark warmup failed")

        wall_samples = []
        tactic_samples = []
        for _ in range(runs):
            _clear_module_build_outputs(worktree, lean_file)
            code, elapsed, output = run_cmd(["lake", "build", module_name], worktree)
            if code != 0:
                raise RuntimeError(output.strip() or "benchmark failed")
            wall_samples.append(elapsed)
            tactic_time = extract_profiler_times(output).get("tactic execution")
            if tactic_time is not None:
                tactic_samples.append(tactic_time)
        return wall_samples, tactic_samples if len(tactic_samples) == runs else None
    finally:
        source_path.write_text(original_source)


def _mean_or_none(samples: list[float] | None) -> float | None:
    if not samples:
        return None
    return statistics.mean(samples)


def _delta(before: float | None, after: float | None) -> float | None:
    if before is None or after is None:
        return None
    return after - before


def _speedup(before: float | None, after: float | None) -> float | None:
    if before is None or after is None or after <= 0:
        return None
    return before / after


def benchmark_change(repo: Path, record: HunkRecord, warmup: int, runs: int) -> TimingResult:
    before_rev = _resolve_rev(repo, f"{record.commit}^")
    after_rev = _resolve_rev(repo, record.commit)

    with tempfile.TemporaryDirectory(prefix="grind-history-") as temp_root:
        temp_root_path = Path(temp_root)
        before_dir = temp_root_path / "before"
        after_dir = temp_root_path / "after"
        try:
            _add_worktree(repo, before_dir, before_rev)
            _add_worktree(repo, after_dir, after_rev)
            before_cache_warning = _maybe_fetch_cache(before_dir)
            after_cache_warning = _maybe_fetch_cache(after_dir)
            if before_cache_warning:
                print(f"  cache warning for {before_rev[:12]}: {before_cache_warning}", flush=True)
            if after_cache_warning:
                print(f"  cache warning for {after_rev[:12]}: {after_cache_warning}", flush=True)
            wall_before, tactic_before = _benchmark_file(before_dir, record.before_file, warmup, runs)
            wall_after, tactic_after = _benchmark_file(after_dir, record.file, warmup, runs)
        except Exception as exc:
            return TimingResult(
                status="error",
                before_rev=before_rev,
                after_rev=after_rev,
                warmup=warmup,
                runs=runs,
                wall_before=[],
                wall_after=[],
                tactic_before=None,
                tactic_after=None,
                wall_mean_before=None,
                wall_mean_after=None,
                wall_delta=None,
                wall_speedup=None,
                tactic_mean_before=None,
                tactic_mean_after=None,
                tactic_delta=None,
                tactic_speedup=None,
                error=str(exc),
            )
        finally:
            _remove_worktree(repo, before_dir)
            _remove_worktree(repo, after_dir)

    wall_mean_before = _mean_or_none(wall_before)
    wall_mean_after = _mean_or_none(wall_after)
    tactic_mean_before = _mean_or_none(tactic_before)
    tactic_mean_after = _mean_or_none(tactic_after)
    return TimingResult(
        status="ok",
        before_rev=before_rev,
        after_rev=after_rev,
        warmup=warmup,
        runs=runs,
        wall_before=wall_before,
        wall_after=wall_after,
        tactic_before=tactic_before,
        tactic_after=tactic_after,
        wall_mean_before=wall_mean_before,
        wall_mean_after=wall_mean_after,
        wall_delta=_delta(wall_mean_before, wall_mean_after),
        wall_speedup=_speedup(wall_mean_before, wall_mean_after),
        tactic_mean_before=tactic_mean_before,
        tactic_mean_after=tactic_mean_after,
        tactic_delta=_delta(tactic_mean_before, tactic_mean_after),
        tactic_speedup=_speedup(tactic_mean_before, tactic_mean_after),
    )


def benchmark_removals(
    repo: Path,
    removals: list[HunkRecord],
    limit: int,
    warmup: int,
    runs: int,
) -> None:
    cache: dict[tuple[str, str], TimingResult] = {}
    for index, record in enumerate(removals[:limit], 1):
        key = (record.commit, record.file)
        if key not in cache:
            print(
                f"Benchmarking {index}/{limit}: {record.file}:L{record.grind_line} at {record.commit[:12]}",
                flush=True,
            )
            cache[key] = benchmark_change(repo, record, warmup, runs)
        record.timing = cache[key]


def _format_mean(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.4f}s"


def _format_speedup(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{value:.3f}x"


def strip_comment(text: str) -> str:
    return text.split("--", 1)[0]


def strip_backticks(text: str) -> str:
    return re.sub(r"`[^`]*`", "", text)


def is_comment_line(text: str) -> bool:
    stripped = text.lstrip()
    return not stripped or stripped.startswith(COMMENT_PREFIXES)


def has_grind_tactic(text: str) -> bool:
    if is_comment_line(text):
        return False
    code = strip_backticks(strip_comment(text))
    return bool(GRIND_RE.search(code))


def has_grind_tactic_call(text: str) -> bool:
    if not has_grind_tactic(text):
        return False
    code = strip_backticks(strip_comment(text))
    return any(pattern.search(code) for pattern in TACTIC_PATTERNS)


def classify_replacement(added_lines: Iterable[str]) -> str:
    code_lines = [line for line in added_lines if not is_comment_line(line)]
    if not code_lines:
        return "unknown-refactor"

    joined = "\n".join(code_lines)
    if any(has_grind_tactic(line) for line in code_lines):
        return "rewritten-still-uses-grind"

    lowered = joined.lower()
    used = [kw for kw in AUTOMATION_KEYWORDS if kw in lowered]
    if used:
        return "replaced-with-other-automation"

    return "replaced-with-manual-proof"


def default_since() -> str:
    return (date.today() - timedelta(days=365 * 2)).isoformat()


HUNK_HEADER_RE = re.compile(r"^@@ -(?P<old>\d+)(?:,\d+)? \+(?P<new>\d+)(?:,\d+)? @@")


def _extract_hunk_old_start(hunk_header: str) -> int | None:
    match = HUNK_HEADER_RE.match(hunk_header)
    if not match:
        return None
    return int(match.group("old"))


def parse_history(log_text: str, include_rewrites: bool) -> tuple[int, list[HunkRecord]]:
    commit_info: CommitInfo | None = None
    current_before_file: str | None = None
    current_file: str | None = None
    current_hunk: str | None = None
    current_old_line: int | None = None
    current_new_line: int | None = None
    removed_lines: list[tuple[int, str]] = []
    added_lines: list[str] = []
    seen_commits: set[str] = set()
    removals: list[HunkRecord] = []

    def flush_hunk() -> None:
        nonlocal removed_lines, added_lines
        if not commit_info or not current_file or not current_hunk:
            removed_lines = []
            added_lines = []
            return
        grind_removed = [(line_no, line) for line_no, line in removed_lines if has_grind_tactic_call(line)]
        if grind_removed:
            classification = classify_replacement(added_lines)
            if classification == "rewritten-still-uses-grind" and not include_rewrites:
                removed_lines = []
                added_lines = []
                return
            removals.append(
                HunkRecord(
                    commit=commit_info.commit,
                    date=commit_info.date,
                    subject=commit_info.subject,
                    before_file=current_before_file or current_file,
                    file=current_file,
                    hunk=current_hunk,
                    grind_line=grind_removed[0][0],
                    removed_lines=[line for _, line in grind_removed],
                    added_lines=list(added_lines),
                    classification=classification,
                )
            )
            seen_commits.add(commit_info.commit)
        removed_lines = []
        added_lines = []

    for raw_line in log_text.splitlines():
        if raw_line == COMMIT_MARKER:
            flush_hunk()
            commit_info = None
            current_before_file = None
            current_file = None
            current_hunk = None
            current_old_line = None
            current_new_line = None
            continue
        if commit_info is None:
            commit = raw_line.strip()
            if not commit:
                continue
            commit_info = CommitInfo(commit=commit, date="", subject="")
            continue
        if not commit_info.date:
            commit_info.date = raw_line.strip()
            continue
        if not commit_info.subject:
            commit_info.subject = raw_line.strip()
            continue
        if raw_line.startswith(DIFF_MARKER):
            flush_hunk()
            current_hunk = None
            current_old_line = None
            current_new_line = None
            parts = raw_line.split()
            current_before_file = parts[2][2:] if len(parts) >= 3 else None
            current_file = parts[3][2:] if len(parts) >= 4 else None
            continue
        if raw_line.startswith("@@"):
            flush_hunk()
            current_hunk = raw_line.strip()
            current_old_line = _extract_hunk_old_start(current_hunk)
            current_new_line = current_old_line
            continue
        if current_hunk is None:
            continue
        if raw_line.startswith("--- ") or raw_line.startswith("+++ "):
            continue
        if raw_line.startswith("-"):
            if current_old_line is not None:
                removed_lines.append((current_old_line, raw_line[1:]))
                current_old_line += 1
        elif raw_line.startswith("+"):
            added_lines.append(raw_line[1:])
            if current_new_line is not None:
                current_new_line += 1
        else:
            if current_old_line is not None:
                current_old_line += 1
            if current_new_line is not None:
                current_new_line += 1

    flush_hunk()
    return len(seen_commits), removals


def build_report(repo: Path, since: str, until: str | None, include_rewrites: bool) -> Report:
    args = [
        "log",
        "--reverse",
        "--date=short",
        f"--since={since}",
        "--format=" + COMMIT_MARKER + "%n%H%n%ad%n%s",
        "--unified=0",
        "-p",
        "-G",
        "grind",
    ]
    if until:
        args.append(f"--until={until}")
    args.extend(["--", LEAN_PATHSPEC])
    log_text = run_git(repo, args)
    commits_with_grind_diffs, removals = parse_history(log_text, include_rewrites)
    counts = Counter(record.classification for record in removals)
    return Report(
        repo=str(repo),
        since=since,
        until=until,
        commits_with_grind_diffs=commits_with_grind_diffs,
        removal_count=len(removals),
        classification_counts=dict(sorted(counts.items())),
        removals=removals,
    )


def print_summary(report: Report, limit: int) -> None:
    print(f"Repo: {report.repo}")
    print(f"Window: {report.since} to {report.until or 'HEAD'}")
    print(f"Commits with grind removals: {report.commits_with_grind_diffs}")
    print(f"Removal hunks: {report.removal_count}")
    if report.classification_counts:
        print("Classification counts:")
        for name, count in report.classification_counts.items():
            print(f"  {name}: {count}")
    print()

    for record in report.removals[:limit]:
        print(f"{record.date} {record.commit[:12]} {record.classification}")
        print(f"  {record.file}:L{record.grind_line}")
        print(f"  {record.subject}")
        if record.timing is not None:
            if record.timing.status == "ok":
                print(
                    "  whole-file wall: "
                    f"{_format_mean(record.timing.wall_mean_before)} -> {_format_mean(record.timing.wall_mean_after)} "
                    f"(delta {_format_mean(record.timing.wall_delta)}, speedup {_format_speedup(record.timing.wall_speedup)})"
                )
                print(
                    "  tactic execution: "
                    f"{_format_mean(record.timing.tactic_mean_before)} -> {_format_mean(record.timing.tactic_mean_after)} "
                    f"(delta {_format_mean(record.timing.tactic_delta)}, speedup {_format_speedup(record.timing.tactic_speedup)})"
                )
            else:
                print(f"  benchmark error: {record.timing.error}")
        for line in record.removed_lines:
            print(f"  - {line.rstrip()}")
        if record.added_lines:
            for line in record.added_lines[:6]:
                print(f"  + {line.rstrip()}")
            if len(record.added_lines) > 6:
                print(f"  + ... ({len(record.added_lines) - 6} more line(s))")
        print()


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Mine git history for removed `grind` tactic calls in Lean files."
    )
    parser.add_argument(
        "repo",
        nargs="?",
        default="mathlib4",
        help="Path to the git repository to scan (default: mathlib4)",
    )
    parser.add_argument(
        "--since",
        default=default_since(),
        help="Start date passed to git log, e.g. 2024-01-01 (default: two years ago)",
    )
    parser.add_argument(
        "--until",
        default=None,
        help="Optional end date passed to git log",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=30,
        help="How many removal hunks to print in the terminal summary",
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Optional path to write the full report as JSON",
    )
    parser.add_argument(
        "--include-rewrites",
        action="store_true",
        help="Include hunks where a removed grind call is replaced by another grind call",
    )
    parser.add_argument(
        "--benchmark-limit",
        type=int,
        default=0,
        help="Benchmark the first N removal hunks as whole files by comparing parent vs removal commit",
    )
    parser.add_argument(
        "--benchmark-warmup",
        type=int,
        default=1,
        help="Warmup runs per revision when benchmarking removals",
    )
    parser.add_argument(
        "--benchmark-runs",
        type=int,
        default=3,
        help="Measured runs per revision when benchmarking removals",
    )
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    report = build_report(repo, args.since, args.until, args.include_rewrites)
    if args.benchmark_limit > 0:
        benchmark_removals(
            repo,
            report.removals,
            args.benchmark_limit,
            args.benchmark_warmup,
            args.benchmark_runs,
        )
    print_summary(report, args.limit)

    if args.output:
        output_path = Path(args.output)
        output_path.write_text(
            json.dumps(
                {
                    **asdict(report),
                    "removals": [asdict(record) for record in report.removals],
                },
                indent=2,
            )
            + "\n"
        )
        print(f"Wrote JSON report to {output_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
