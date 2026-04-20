#!/usr/bin/env python3
"""Nightly evaluation entry point.

Clones mathlib4 (if needed), checks out a pinned commit, then benchmarks
the decompiler on each Lean file containing `grind` in the given path.
"""
import argparse
import http.server
import json
import re
import shutil
import subprocess
import sys
import webbrowser
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


def build_lean_decomp(workspace: Path):
    print("Building lean-decomp...")
    run(["lake", "build"], cwd=workspace)


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
            if re.search(r'(?<!\w)grind(?=\s|\[|$)', line):
                result.append(f)
                break
    return result


def serve_results(results_path: Path, workspace: Path, port: int = 8080):
    """Start a local HTTP server serving eval-live with the results JSON."""
    import eval_live
    css = eval_live.css()
    js = eval_live.js()
    results_json = results_path.read_text()
    name = "LeanDecomp"

    # Read the Python library and graph script
    eval_live_py = eval_live.pyodide_lib()
    graph_script_path = workspace / "scripts" / "graphs.py"
    graph_script = graph_script_path.read_text() if graph_script_path.exists() else ""

    # Escape Python sources for embedding in JS
    eval_live_py_js = json.dumps(eval_live_py)
    graph_script_js = json.dumps(graph_script)

    pyodide_tag = ""
    init_graphs_args = ""
    if graph_script:
        pyodide_tag = '<script src="https://cdn.jsdelivr.net/pyodide/v0.27.5/full/pyodide.js"></script>'
        init_graphs_args = f", {graph_script_js}, {eval_live_py_js}"

    page = f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Eval Live</title>
  <style>
    body {{
      font-family: system-ui, -apple-system, sans-serif;
      margin: 0; padding: 2rem 3rem;
      background: #f5f6f8; color: #1a1a1a;
    }}
    {css}
  </style>
  {pyodide_tag}
</head>
<body>
  <div id="tables"></div>
  <script>
    {js}
    initEvalLive("tables", {results_json}, "{name}"{init_graphs_args});
  </script>
</body>
</html>"""
    page_bytes = page.encode()

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.send_header("Content-Length", str(len(page_bytes)))
            self.end_headers()
            self.wfile.write(page_bytes)

        def log_message(self, fmt, *a):
            pass  # silence request logs

    server = http.server.HTTPServer(("", port), Handler)
    url = f"http://localhost:{port}"
    print(f"\nServing eval-live at {url}  (Ctrl-C to stop)")
    webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServer stopped.")


def main():
    parser = argparse.ArgumentParser(
        description="Nightly evaluation: benchmark grind variants across mathlib files."
    )
    parser.add_argument("path", nargs="?", default=None,
                        help="Lean file or folder to evaluate (relative to workspace, default: mathlib4/Mathlib/Algebra)")
    parser.add_argument("--output", default="results.json",
                        help="Path to write JSON results database (default: results.json)")
    parser.add_argument("--serve", action="store_true",
                        help="Start a local HTTP server to view results after benchmarking")
    parser.add_argument("--justserve", action="store_true",
                        help="Skip benchmarking and just serve existing results")
    parser.add_argument("--port", type=int, default=8080,
                        help="Port for the eval-live server (default: 8080)")
    add_bench_args(parser)
    args = parser.parse_args()

    workspace = Path(__file__).resolve().parents[1]
    if args.dump is not None:
        dump_path = Path(args.dump)
        if not dump_path.is_absolute():
            dump_path = workspace / dump_path
        args.dump = str(dump_path.resolve())
        # Remove previously dumped Lean files but keep Lake cache (.lake/,
        # lakefile.lean, lake-manifest.json, symlinks) to avoid rebuilding deps.
        _KEEP_IN_DUMP = {".lake", "mathlib4", "lean-toolchain", "lakefile.lean", "lake-manifest.json"}
        if dump_path.exists():
            for child in dump_path.iterdir():
                if child.name not in _KEEP_IN_DUMP:
                    print(f"Removing stale dump content: {child}")
                    if child.is_dir() and not child.is_symlink():
                        shutil.rmtree(child)
                    else:
                        child.unlink()

    if args.justserve:
        results = Path(args.output)
        if not results.is_absolute():
            results = workspace / results
        if not results.exists():
            print(f"Results file not found: {results}", file=sys.stderr)
            return 2
        serve_results(results, workspace, args.port)
        return 0

    mathlib = ensure_mathlib(workspace)
    build_lean_decomp(workspace)

    if args.path is None:
        target = mathlib / "Mathlib" / "Algebra" / "Order" / "Group"
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
        bench_grind(str(rel), mathlib, args, db=db)

    db.save_json(args.output)
    print(f"\nResults saved to {args.output}")

    if args.serve:
        serve_results(Path(args.output).resolve(), workspace, args.port)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
