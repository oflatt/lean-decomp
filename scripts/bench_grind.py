#!/usr/bin/env python3
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


def extract_profiler_line(output: str, theorem_name: str):
    # Keep this permissive; Lean profiler format can vary across versions.
    pattern = re.compile(rf".*{re.escape(theorem_name)}.*", re.IGNORECASE)
    for line in output.splitlines():
        if pattern.match(line):
            return line.strip()
    return None


def format_stats(samples):
    return {
        "count": len(samples),
        "mean": statistics.mean(samples),
        "median": statistics.median(samples),
        "stdev": statistics.stdev(samples) if len(samples) > 1 else 0.0,
        "min": min(samples),
        "max": max(samples),
    }


def main():
    parser = argparse.ArgumentParser(
        description="Benchmark proof-search time for BenchGrind theorem via `lake env lean`."
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
    parser.add_argument(
        "--prepare",
        action="store_true",
        help="Run `lake build LeanDecomp.bigstep` once before benchmarking",
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

    if args.prepare:
        print("Preparing imports with: lake build LeanDecomp.bigstep")
        code, elapsed, output = run_cmd(["lake", "build", "LeanDecomp.bigstep"], workspace)
        print(f"  prepare exit={code} time={elapsed:.3f}s")
        if code != 0:
            print(output)
            return code

    cmd = ["lake", "env", "lean", args.lean_file]
    print(f"Benchmark command: {' '.join(cmd)}")
    print(f"Workspace: {workspace}")
    print(f"Warmup runs: {args.warmup}")
    print(f"Measured runs: {args.runs}")

    for i in range(args.warmup):
        code, elapsed, output = run_cmd(cmd, workspace)
        print(f"warmup {i + 1}/{args.warmup}: {elapsed:.3f}s (exit={code})")
        if code != 0:
            print(output)
            return code

    samples = []
    profiler_hits = []
    for i in range(args.runs):
        code, elapsed, output = run_cmd(cmd, workspace)
        print(f"run {i + 1}/{args.runs}: {elapsed:.3f}s (exit={code})")
        if code != 0:
            print(output)
            return code

        samples.append(elapsed)
        hit = extract_profiler_line(output, args.theorem)
        if hit:
            profiler_hits.append(hit)

    stats = format_stats(samples)
    print("\nTiming summary (seconds):")
    print(f"  count:  {stats['count']}")
    print(f"  mean:   {stats['mean']:.4f}")
    print(f"  median: {stats['median']:.4f}")
    print(f"  stdev:  {stats['stdev']:.4f}")
    print(f"  min:    {stats['min']:.4f}")
    print(f"  max:    {stats['max']:.4f}")

    if profiler_hits:
        print("\nProfiler lines mentioning theorem:")
        # Deduplicate while preserving order.
        seen = set()
        for line in profiler_hits:
            if line not in seen:
                seen.add(line)
                print(f"  {line}")
    else:
        print("\nNo profiler line matched theorem name; wall-clock timing above is still valid.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
