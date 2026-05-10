#!/usr/bin/env python3
"""analyze.py — bucket failures from a `nightly.py` results JSON, and
optionally diff two sweep results.

Subcommands:
  bucket  RESULTS_JSON [DUMP_ROOT]
      Print a per-cluster failure breakdown for the given results file.
      If DUMP_ROOT is provided, the success count is computed from the
      number of `*.decompile.lean` files (i.e. validated suggestions)
      and used to compute a coverage percentage.

  diff   OLD_JSON NEW_JSON
      Compare two sweep results.  Reports cluster delta and per-site
      changes (newly-failing, newly-passing, error-shape change).

Exit codes:
  0  success
  1  malformed input or missing file
  2  bad arguments

Failure cluster heuristics (matched in order, first hit wins):
  wall-clock-timeout   "[timeout"
  heartbeat            "maxHeartbeats" or "heartbeats"
  too-large            "too large"
  cross-file-inst      "inst✝" (escaped)
  parse-error          "unexpected token"
  validate-fallback    "did not re-elaborate" or "unsolved goals"
  other                anything else
"""
import argparse
import collections
import json
import re
import sys
from pathlib import Path


CLUSTER_RULES = [
    ("wall-clock-timeout", lambda m: "[timeout" in m),
    ("heartbeat", lambda m: "maxHeartbeats" in m or "heartbeats" in m.lower()),
    ("too-large", lambda m: "too large" in m),
    # `inst<U+271D>` is Lean's PrettyPrinter inaccessibility marker (LATIN CROSS).
    # Test the codepoint, not the literal char, so source-file editors can't
    # mangle it.
    ("cross-file-inst", lambda m: "inst✝" in m),
    ("parse-error", lambda m: "unexpected token" in m),
    ("validate-fallback", lambda m: "did not re-elaborate" in m or "unsolved goals" in m),
    ("other", lambda _m: True),
]


def classify(msg: str) -> str:
    for name, pred in CLUSTER_RULES:
        if pred(msg):
            return name
    return "other"


def load_errors(path: Path, treatment: str | None = "decompile") -> list[dict]:
    """Load errors from a nightly results JSON, filtered by treatment.

    By default returns only `decompile` treatment errors — comparison /
    bucketing across treatments is misleading because each treatment has
    its own failure modes (`grindscript` failures use `#abc1` opaque
    refs, etc.).  Pass `treatment=None` for all.
    """
    with path.open() as f:
        data = json.load(f)
    if not isinstance(data, dict) or "errors" not in data:
        raise SystemExit(f"{path}: not a nightly.py results JSON")
    errs = data["errors"]
    if treatment is not None:
        errs = [e for e in errs if e.get("treatment") == treatment]
    return errs


def site_key(e: dict) -> str:
    return f"{e['file']}:L{e['grind_line']}"


def count_total_sites(dump_root: Path | None) -> int | None:
    """Count grind sites by counting *.decompile.query.lean dump artifacts.
    Returns None when no dump root or it doesn't exist."""
    if dump_root is None or not dump_root.exists():
        return None
    n = 0
    for p in dump_root.rglob("*.decompile.query.lean"):
        n += 1
    return n


def cmd_bucket(args: argparse.Namespace) -> int:
    treatment = None if args.treatment == "all" else args.treatment
    errors = load_errors(Path(args.results), treatment=treatment)
    dump_root = Path(args.dump_root) if args.dump_root else None
    n_total = count_total_sites(dump_root)
    n_failures = len(errors)

    print(f"{Path(args.results).name} (treatment={args.treatment}):")
    if n_total is not None:
        n_success = n_total - n_failures
        pct = 100 * n_success / n_total if n_total > 0 else 0
        print(f"  sites:    {n_total} (counted from {dump_root}/**.decompile.query.lean)")
        print(f"  success:  {n_success}/{n_total} = {pct:.0f}%")
    else:
        print(f"  (no --dump-root given; can't compute coverage)")
    print(f"  failures: {n_failures}")
    print()

    buckets: collections.Counter = collections.Counter()
    sites_per_bucket: dict[str, list[str]] = collections.defaultdict(list)
    for e in errors:
        b = classify(e.get("error", ""))
        buckets[b] += 1
        sites_per_bucket[b].append(site_key(e))

    print("Cluster breakdown:")
    for k, v in sorted(buckets.items(), key=lambda x: -x[1]):
        print(f"  {v:3d}  {k}")
    print()

    if args.show_sites:
        for k, v in sorted(buckets.items(), key=lambda x: -x[1]):
            print(f"-- {k} ({v}) --")
            for s in sites_per_bucket[k]:
                print(f"    {s}")
    return 0


def cmd_diff(args: argparse.Namespace) -> int:
    old_errors = load_errors(Path(args.old))
    new_errors = load_errors(Path(args.new))

    old_index = {site_key(e): e for e in old_errors}
    new_index = {site_key(e): e for e in new_errors}

    old_sites = set(old_index)
    new_sites = set(new_index)

    fixed = sorted(old_sites - new_sites)  # were failing, no longer failing
    regressed = sorted(new_sites - old_sites)  # were passing, now failing
    persistent = sorted(old_sites & new_sites)

    shape_changed = []
    shape_same = []
    for s in persistent:
        old_b = classify(old_index[s].get("error", ""))
        new_b = classify(new_index[s].get("error", ""))
        if old_b != new_b:
            shape_changed.append((s, old_b, new_b))
        else:
            shape_same.append((s, old_b))

    print(f"OLD: {Path(args.old).name}  ({len(old_errors)} failures)")
    print(f"NEW: {Path(args.new).name}  ({len(new_errors)} failures)")
    print()
    print(f"  fixed (was failing, now passing):    {len(fixed)}")
    print(f"  regressed (was passing, now failing): {len(regressed)}")
    print(f"  persistent (still failing):          {len(persistent)}")
    print(f"    └ shape change in error message:   {len(shape_changed)}")
    print()

    def _section(title: str, items: list, fmt):
        if not items:
            return
        print(f"-- {title} ({len(items)}) --")
        for it in items:
            print(f"    {fmt(it)}")
        print()

    _section("FIXED", fixed, lambda s: s)
    _section("REGRESSED", regressed,
             lambda s: f"{s}  [{classify(new_index[s].get('error', ''))}]")
    _section("PERSISTENT (shape changed)", shape_changed,
             lambda t: f"{t[0]}  {t[1]} → {t[2]}")

    if args.show_persistent_same:
        _section("PERSISTENT (same shape)", shape_same,
                 lambda t: f"{t[0]}  [{t[1]}]")
    return 0


# ---------------------------------------------------------------------------
# Output-shape detector
# ---------------------------------------------------------------------------

# A "fallback shape" suggests the structural decomp didn't get traction:
# the macro emitted a giant `exact` term, a `with_unfolding_all exact`, or a
# `grind only [...]` leaf.  These are technically successes (the suggestion
# re-elaborated) but indicate handlers we should add.

# Threshold (chars) above which an `exact <term>` is considered "big".
BIG_EXACT_CHARS = 500


def detect_fallback_shapes(text: str) -> dict[str, int]:
    """Count fallback-shape occurrences in a rendered tactic block."""
    counts = {
        "with_unfolding_all_exact": text.count("with_unfolding_all"),
        "grind_only_leaf": text.count("grind only ["),
        "big_exact": 0,
    }
    # Approximate "big exact": find lines starting with `exact ` whose
    # text-extent (until next blank line or non-indented line) is >threshold.
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.lstrip()
        if stripped.startswith("exact ") or stripped == "exact":
            # Capture until indentation drops back to start-of-tactic level
            base_indent = len(line) - len(stripped)
            j = i + 1
            block = line
            while j < len(lines):
                next_line = lines[j]
                next_indent = len(next_line) - len(next_line.lstrip())
                if next_line.strip() == "" or next_indent <= base_indent:
                    break
                block += next_line
                j += 1
            if len(block) > BIG_EXACT_CHARS:
                counts["big_exact"] += 1
            i = j
        else:
            i += 1
    return counts


def cmd_shape(args: argparse.Namespace) -> int:
    """Walk *.decompile.lean files in a dump dir, report per-file shape stats."""
    dump_root = Path(args.dump_root)
    if not dump_root.exists():
        raise SystemExit(f"dump dir not found: {dump_root}")
    # We want the success-emission files, not the failed/query ones.
    # `nightly.py --dump` writes `<...>/L<N>.decompile.lean` for successes.
    decompile_files = sorted(
        p for p in dump_root.rglob("*.decompile.lean")
        if not p.name.endswith(".query.lean")
        and not p.name.endswith(".failed.lean")
    )
    if not decompile_files:
        print(f"no .decompile.lean files under {dump_root}")
        return 0

    totals = {"with_unfolding_all_exact": 0, "grind_only_leaf": 0, "big_exact": 0}
    flagged: list[tuple[Path, dict[str, int], int]] = []
    for f in decompile_files:
        text = f.read_text()
        # Heuristic: only look at the LAST tactic block (the one our macro
        # added).  Diff against the original would be cleaner but harder.
        # As a proxy, scan the whole file for fallback markers and trust
        # they came from us.
        counts = detect_fallback_shapes(text)
        for k, v in counts.items():
            totals[k] += v
        size = sum(counts.values())
        if size > 0:
            flagged.append((f, counts, size))

    print(f"Scanned {len(decompile_files)} *.decompile.lean files under {dump_root}.")
    print()
    print("Total fallback-shape occurrences:")
    for k, v in totals.items():
        print(f"  {v:4d}  {k}")
    print()

    if not flagged:
        print("No fallback shapes detected — everything is structural.")
        return 0

    flagged.sort(key=lambda t: -t[2])
    print(f"Per-file (top {min(args.top, len(flagged))} by total fallback count):")
    for f, counts, size in flagged[: args.top]:
        rel = f.relative_to(dump_root)
        parts = [f"{c}={counts[c]}" for c in counts if counts[c] > 0]
        print(f"  {size:3d}  {rel}  ({', '.join(parts)})")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    pb = sub.add_parser("bucket", help="Bucket failures from one results JSON.")
    pb.add_argument("results", help="Path to results JSON (e.g. results-broader-order.json)")
    pb.add_argument("dump_root", nargs="?", default=None,
                    help="Optional dump dir for coverage % (counts *.decompile.query.lean)")
    pb.add_argument("--show-sites", action="store_true",
                    help="List per-site identifiers in each cluster")
    pb.add_argument("--treatment", default="decompile",
                    help="Filter errors to this treatment (default: decompile; pass 'all' for no filter)")

    pd = sub.add_parser("diff", help="Diff two results JSONs.")
    pd.add_argument("old", help="Older results JSON")
    pd.add_argument("new", help="Newer results JSON")
    pd.add_argument("--show-persistent-same", action="store_true",
                    help="Also list persistent failures whose shape didn't change")

    ps = sub.add_parser("shape", help="Detect fallback-shape patterns in dumped suggestions.")
    ps.add_argument("dump_root", help="Dump directory (e.g. dump-broader-order)")
    ps.add_argument("--top", type=int, default=20,
                    help="Show top N flagged files (default 20)")

    args = p.parse_args()
    if args.cmd == "bucket":
        return cmd_bucket(args)
    if args.cmd == "diff":
        return cmd_diff(args)
    if args.cmd == "shape":
        return cmd_shape(args)
    return 2


if __name__ == "__main__":
    sys.exit(main())
