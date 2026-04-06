#!/usr/bin/env python3
"""Nightly evaluation entry point.

Clones mathlib4 (if needed), checks out a pinned commit, then runs
bench_grind.py on each Lean file containing `grind` in the given path.
"""
import argparse
import subprocess
import sys
from pathlib import Path

from bench_db import BenchDB
from bench_grind import add_bench_args, bench_grind

MATHLIB_REPO = "https://github.com/leanprover-community/mathlib4"
MATHLIB_COMMIT = "d4c205d5773673a2e8112f8c72bf33a0358e333d"
MATHLIB_DIR = "mathlib4"


def run(cmd, **kwargs):
    print(f"$ {' '.join(str(c) for c in cmd)}")
    proc = subprocess.run(cmd, **kwargs)
    if proc.returncode != 0:
        print(f"Command failed with exit code {proc.returncode}", file=sys.stderr)
        sys.exit(proc.returncode)


def ensure_mathlib(workspace: Path):
    mathlib = workspace / MATHLIB_DIR
    if not mathlib.exists():
        print(f"Cloning mathlib4 into {mathlib}...")
        run(["git", "clone", MATHLIB_REPO, str(mathlib)])
    else:
        print(f"mathlib4 already present at {mathlib}")

    # Reset any leftover modifications from previous runs
    run(["git", "checkout", "."], cwd=mathlib)

    print(f"Checking out {MATHLIB_COMMIT}...")
    run(["git", "checkout", MATHLIB_COMMIT], cwd=mathlib)

    # Add lean-decomp as a local dependency so the decompile tactic is available
    lakefile = mathlib / "lakefile.lean"
    manifest = mathlib / "lake-manifest.json"
    dep_line = f'require "lean-decomp" from "{workspace}"'
    text = lakefile.read_text()
    needs_update = dep_line not in text
    if needs_update:
        print("Adding lean-decomp dependency to mathlib lakefile...")
        lakefile.write_text(text + "\n" + dep_line + "\n")
    # Also update manifest if lean-decomp isn't registered there
    manifest_text = manifest.read_text() if manifest.exists() else ""
    if needs_update or "lean-decomp" not in manifest_text:
        run(["lake", "update", "lean-decomp"], cwd=mathlib)

    return mathlib


def find_lean_files_with_grind(path: Path) -> list[Path]:
    """Recursively find .lean files that contain a grind tactic call."""
    if path.is_file():
        files = [path] if path.suffix == ".lean" else []
    else:
        files = sorted(path.rglob("*.lean"))

    result = []
    for f in files:
        try:
            text = f.read_text()
        except (OSError, UnicodeDecodeError):
            continue
        for line in text.splitlines():
            trimmed = line.lstrip()
            if trimmed.startswith("grind ") or trimmed.startswith("grind[") or trimmed == "grind":
                result.append(f)
                break
    return result


def main():
    parser = argparse.ArgumentParser(
        description="Nightly evaluation: benchmark grind variants across mathlib files."
    )
    parser.add_argument("path", nargs="?", default=None,
                        help="Lean file or folder to evaluate (relative to workspace, default: mathlib4/Mathlib/Algebra)")
    parser.add_argument("--output", default="results.json",
                        help="Path to write JSON results database (default: results.json)")
    add_bench_args(parser)
    args = parser.parse_args()

    workspace = Path(__file__).resolve().parents[1]
    mathlib = ensure_mathlib(workspace)

    if args.path is None:
        target = mathlib / "Mathlib" / "Algebra"
    else:
        target = workspace / args.path
    if not target.exists():
        print(f"Not found: {target}", file=sys.stderr)
        return 2

    lean_files = find_lean_files_with_grind(target)
    print(f"\nFound {len(lean_files)} file(s) containing grind in {target}")
    if not lean_files:
        return 0

    # Build the target files (and their dependencies)
    modules = [
        str(f.relative_to(mathlib)).removesuffix(".lean").replace("/", ".")
        for f in lean_files
    ]
    print(f"\nBuilding {len(modules)} module(s)...")
    run(["lake", "build"] + modules, cwd=mathlib)

    # Benchmark each file
    db = BenchDB()
    for i, f in enumerate(lean_files, 1):
        rel = f.relative_to(mathlib)
        print(f"\n{'='*60}")
        print(f"[{i}/{len(lean_files)}] {rel}")
        print(f"{'='*60}")
        rc = bench_grind(str(rel), mathlib, args, db=db)
        if rc != 0:
            print(f"  bench_grind failed for {rel} (exit {rc})")

    db.save_json(args.output)
    print(f"\nResults saved to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
