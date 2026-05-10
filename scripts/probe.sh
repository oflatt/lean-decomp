#!/usr/bin/env bash
# probe.sh — inspect a single decompile failure with elevated heartbeats.
#
# Usage:
#   scripts/probe.sh <path/to/Foo.lean> <line> [maxHeartbeats] [--dump <dir>]
#                                                              [--profile] [--dumpOnFail]
#
# Workflow:
#   1. Locate <dump-root>/<basename>/L<line>.decompile.query.lean
#      Default dump-root search: any `dump-*` directory under workspace.
#      Specify a fixed root via `--dump <dir>` (e.g. `--dump dump-broader-order`).
#   2. Copy to /tmp/lean-decomp-probe.lean with options injected after the
#      existing `set_option profiler true` line:
#        - `set_option maxHeartbeats N` (default 8000000 = 40× file default)
#        - `set_option leanDecomp.profile true` if `--profile` given
#        - `set_option leanDecomp.dumpOnFail true` if `--dumpOnFail` given
#   3. Run `lake env lean` from mathlib4/, capturing output.
#
# Why: when a decompile times out at the default 200k budget, the macro hits
# the timeout silently (the message log gets reset before exit, see the
# state-monad refactor README entry).  Re-running with elevated heartbeats
# either succeeds (so we see the candidate tactics that hit the budget) or
# fails differently (giving us a useful diagnostic).

set -euo pipefail

WORKSPACE="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
  cat >&2 <<'EOF'
Usage: scripts/probe.sh <file> <line> [maxHeartbeats] [--dump <dir>] [--profile] [--dumpOnFail]

  <file>          Mathlib path or basename (e.g. mathlib4/Mathlib/Algebra/.../Sum.lean
                  or just "Sum.lean").
  <line>          The grind line number to probe (matches L<N>.decompile.query.lean).
  [maxHeartbeats] Optional positional 3rd arg, overrides set_option maxHeartbeats
                  (default 8000000).
  --dump <dir>    Search a specific dump root (e.g. dump-broader-order).
                  Default searches all `dump-*` dirs under the workspace.
  --profile       Inject `set_option leanDecomp.profile true` for per-phase markers.
  --dumpOnFail    Inject `set_option leanDecomp.dumpOnFail true`; failure dump
                  paths are reported in the macro's error message.

Example:
  scripts/probe.sh Rat.lean 89 --dump dump-broader-order --profile --dumpOnFail
  scripts/probe.sh mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean 36
EOF
  exit 2
}

if [[ $# -lt 2 ]]; then
  usage
fi

FILE_ARG="$1"
LINE="$2"
shift 2
MAX_HB=8000000
DUMP_ROOT=""
INJECT_PROFILE=0
INJECT_DUMPONFAIL=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --dump)
      DUMP_ROOT="$2"
      shift 2
      ;;
    --profile)
      INJECT_PROFILE=1
      shift
      ;;
    --dumpOnFail)
      INJECT_DUMPONFAIL=1
      shift
      ;;
    --help|-h)
      usage
      ;;
    *)
      # Treat first remaining bareword as MAX_HB (back-compat with positional 3rd arg)
      if [[ "$1" =~ ^[0-9]+$ ]]; then
        MAX_HB="$1"
        shift
      else
        echo "unknown option: $1" >&2
        usage
      fi
      ;;
  esac
done

# Strip mathlib4/ prefix if present, normalise to bare basename for dump-dir lookup.
BASENAME="$(basename "${FILE_ARG%.lean}")"

# Resolve the search root(s).  When `--dump <dir>` is given, search only that.
# Otherwise, search every `dump-*` dir under the workspace.
QUERY=""
if [[ -n "$DUMP_ROOT" ]]; then
  # Allow either an absolute path or a workspace-relative dir.
  if [[ "$DUMP_ROOT" != /* ]]; then
    DUMP_ROOT="$WORKSPACE/$DUMP_ROOT"
  fi
  if [[ ! -d "$DUMP_ROOT" ]]; then
    echo "--dump dir does not exist: $DUMP_ROOT" >&2
    exit 1
  fi
  QUERY="$(find "$DUMP_ROOT" -path "*/${BASENAME}/L${LINE}.decompile.query.lean" -print -quit 2>/dev/null || true)"
else
  for DUMP_DIR in "$WORKSPACE"/dump-*; do
    [[ -d "$DUMP_DIR" ]] || continue
    CANDIDATE="$(find "$DUMP_DIR" -path "*/${BASENAME}/L${LINE}.decompile.query.lean" -print -quit 2>/dev/null || true)"
    if [[ -n "$CANDIDATE" ]]; then
      QUERY="$CANDIDATE"
      break
    fi
  done
fi

if [[ -z "$QUERY" ]]; then
  ROOT_DESC="${DUMP_ROOT:-dump-*}"
  echo "no L${LINE}.decompile.query.lean found under ${ROOT_DESC}/.../${BASENAME}/" >&2
  echo "did you run nightly with --dump <dir>?" >&2
  exit 1
fi

PROBE=/tmp/lean-decomp-probe.lean

# Inject options after the existing `set_option profiler true` line.  awk
# matches the line and inserts requested set_options below it.
awk \
    -v hb="$MAX_HB" \
    -v profile="$INJECT_PROFILE" \
    -v dumpOnFail="$INJECT_DUMPONFAIL" '
  /^set_option profiler true$/ {
    print
    print "set_option maxHeartbeats " hb
    if (profile == "1") print "set_option leanDecomp.profile true"
    if (dumpOnFail == "1") print "set_option leanDecomp.dumpOnFail true"
    next
  }
  { print }
' "$QUERY" > "$PROBE"

echo "probe: $QUERY"
echo "  → $PROBE  (maxHeartbeats=$MAX_HB, profile=$INJECT_PROFILE, dumpOnFail=$INJECT_DUMPONFAIL)"
echo

cd "$WORKSPACE/mathlib4"
exec lake env lean "$PROBE"
