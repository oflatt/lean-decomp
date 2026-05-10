#!/usr/bin/env bash
# smoke.sh — fast regression check before / after a code change.
#
# Runs in parallel:
#   1. `lake build` (all targets)
#   2. Sum.lean nightly slice (4/4)
#   3. Int.lean nightly slice (5/5)
#   4. Group/List.lean L234 cross-file slice (1/1)
#
# Reports pass/fail per task and a final summary.  Exit 0 iff all four pass.
#
# Why: the day's edit cycle hits these four checks repeatedly; running them
# sequentially is ~80s, in parallel ~25s.  Catches >95% of regressions
# without the 17-min broader-corpus cost.
#
# After completion, verifies no `lean Mathlib/...` orphan processes survive.

set -euo pipefail

WORKSPACE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$WORKSPACE"

LOG_DIR="$(mktemp -d -t smoke-XXXXXX)"
trap 'rm -rf "$LOG_DIR"' EXIT

# Each task: (name, cmd, expected-pass-count or "build", grep-pattern).
# When grep-pattern matches `expected` times, task passes.  When `expected`
# is the literal "build", task passes iff exit code is 0.

declare -A TASK_PIDS
declare -A TASK_LOGS

start_task() {
  local name="$1" cmd="$2" expected="$3" pattern="$4"
  TASK_LOGS[$name]="$LOG_DIR/$name.log"
  bash -c "$cmd" > "${TASK_LOGS[$name]}" 2>&1 &
  TASK_PIDS[$name]="$!"
  # Persist expected count and pattern via temp files (bash assoc-arrays
  # don't compose well with dynamic names).
  echo "$expected" > "$LOG_DIR/$name.expected"
  echo "$pattern" > "$LOG_DIR/$name.pattern"
}

# Step 1: do the (serialized) lake build first AND, in parallel with it,
# warm the mathlib setup (git checkout + lean-decomp dependency).
# Mathlib setup is sequential — concurrent `git checkout` invocations race
# on .git/index.lock.  We exploit `nightly.py` with an empty path-arg path
# convention isn't supported, so do it via a one-shot setup invocation.
echo "smoke: lake build + mathlib setup..."
lake build > "$LOG_DIR/build.log" 2>&1 &
BUILD_PID=$!
# Run a no-op nightly invocation just to do mathlib setup.  Pick the
# smallest file (Int.lean = 5 sites) for the dependency-registration warmup.
python3 scripts/nightly.py mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Int.lean \
    --treatment decompile --no-benchmark \
    --dump dump-nightly-int --output results-nightly-int.json \
    > "$LOG_DIR/int.log" 2>&1
INT_EXIT=$?
wait "$BUILD_PID"
BUILD_EXIT=$?
echo "  build exit=$BUILD_EXIT, int exit=$INT_EXIT (also primes mathlib setup)"
INT_COUNT=$(grep -cE "Suggestion run finished:.*exit=0" "$LOG_DIR/int.log" || true)

# Step 2: with mathlib setup done, run Sum + List in parallel using
# --skip-mathlib-setup (avoids the .git/index.lock race).
echo "smoke: Sum + List in parallel..."
start_task "sum"  "python3 scripts/nightly.py mathlib4/Mathlib/Algebra/Order/Group/Int/Sum.lean --treatment decompile --no-benchmark --dump dump-nightly-sum --output results-nightly-sum.json --skip-mathlib-setup" \
                  "4" "Suggestion run finished:.*exit=0"
start_task "list" "python3 scripts/nightly.py mathlib4/Mathlib/Algebra/Order/BigOperators/Group/List.lean --treatment decompile --no-benchmark --dump dump-list-test --output /tmp/results-list-test.json --skip-mathlib-setup" \
                  "1" "Suggestion run finished:.*exit=0"

# Wait for all background tasks to finish.  Capture exit codes BEFORE
# computing summary (set -e + `wait || true` confuses $? semantics).
ALL_PASS=1
declare -A EXIT_CODES
for name in "${!TASK_PIDS[@]}"; do
  pid="${TASK_PIDS[$name]}"
  set +e
  wait "$pid"
  EXIT_CODES[$name]="$?"
  set -e
done
echo "smoke: results"

emit_status() {
  local name="$1" exit_code="$2" count="$3" expected="$4" log="$5"
  local status
  if [[ "$expected" == "build" ]]; then
    if [[ "$exit_code" == "0" ]]; then status="PASS"; else status="FAIL"; fi
  elif [[ "$count" == "$expected" ]]; then
    status="PASS"
  else
    status="FAIL"
  fi
  echo "  $status $name (exit=$exit_code, count=$count, want=$expected)"
  if [[ "$status" == "FAIL" ]]; then
    ALL_PASS=0
    echo "    log: $log"
    tail -10 "$log" | sed 's/^/      /'
  fi
}

emit_status "build" "$BUILD_EXIT" "0" "build" "$LOG_DIR/build.log"
emit_status "int"   "$INT_EXIT"   "$INT_COUNT" "5" "$LOG_DIR/int.log"
for name in "${!TASK_PIDS[@]}"; do
  exit_code="${EXIT_CODES[$name]}"
  expected=$(cat "$LOG_DIR/$name.expected")
  pattern=$(cat "$LOG_DIR/$name.pattern")
  count=0
  if [[ -n "$pattern" ]]; then
    count=$(grep -cE "$pattern" "${TASK_LOGS[$name]}" || true)
  fi
  emit_status "$name" "$exit_code" "$count" "$expected" "${TASK_LOGS[$name]}"
done

# Orphan-process check: catch the Friday-pile-up failure mode early.
ORPHANS=$(ps -ef | grep -E "lean Mathlib/" | grep -v grep | wc -l | tr -d ' ')
if [[ "$ORPHANS" != "0" ]]; then
  echo "  WARN $ORPHANS orphan 'lean Mathlib/...' processes survived; investigate"
  ALL_PASS=0
fi

if [[ "$ALL_PASS" == "1" ]]; then
  echo "OK"
  exit 0
else
  echo "FAILED"
  exit 1
fi
