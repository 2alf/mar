#!/usr/bin/env bash
# Build the formalization and check the axioms of every result.
#
#   ./verify.sh [--max-gb N] [--skip-cache]
#
# 1. lake exe cache get   (Mathlib build cache; skip with --skip-cache)
# 2. lake build           (MonsterCN and MAR)
# 3. lake env lean check_axioms.lean, and check that every result depends only on
#    propext, Classical.choice and Quot.sound.
# Steps 2 and 3 run under a memory guard that kills any lean process started by this script once
# its resident memory exceeds N GB (default 12). Logs are written to verify_logs/.
set -u
MAX_GB=12; SKIP_CACHE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --max-gb) MAX_GB="$2"; shift 2 ;;
    --skip-cache) SKIP_CACHE=1; shift ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
ROOT="$(cd "$(dirname "$0")" && pwd)"; cd "$ROOT"
LOGS="$ROOT/verify_logs"; mkdir -p "$LOGS"
LIMIT_KB=$(awk -v g="$MAX_GB" 'BEGIN { printf "%d", g * 1024 * 1024 }')
GUARD_LOG="$LOGS/guard.log"; : > "$GUARD_LOG"

guard() {
  local pre; pre=" $(ps -A -o pid=,comm= | awk '$2 ~ /(^|\/)lean$/ {print $1}' | tr '\n' ' ') "
  while true; do
    ps -A -o pid=,rss=,comm= | awk '$3 ~ /(^|\/)lean$/ {print $1, $2}' | while read -r pid rss; do
      case "$pre" in *" $pid "*) continue ;; esac
      if [ "$rss" -gt "$LIMIT_KB" ]; then
        echo "killed lean PID $pid at $((rss / 1024)) MB" >> "$GUARD_LOG"; kill -9 "$pid" 2>/dev/null
      fi
    done
    sleep 2
  done
}

run_guarded() {
  local name="$1"; shift
  guard & local gpid=$!
  "$@" 2>&1 | tee "$LOGS/$name.log"; local rc=${PIPESTATUS[0]}
  kill "$gpid" 2>/dev/null; wait "$gpid" 2>/dev/null
  if [ -s "$GUARD_LOG" ]; then cat "$GUARD_LOG"; return 1; fi
  return "$rc"
}

if [ "$SKIP_CACHE" -eq 0 ]; then echo "=== lake exe cache get"; lake exe cache get; fi

echo "=== lake build (memory guard: $MAX_GB GB per lean process)"
if ! run_guarded build lake build; then echo "FAILED: lake build"; echo "Verification FAILED."; exit 1; fi

echo "=== lake env lean check_axioms.lean"
run_guarded axioms lake env lean check_axioms.lean; rc=$?
expected=$(grep -c '^#print axioms ' check_axioms.lean)
ok=0; bad=0
while IFS= read -r line; do
  case "$line" in
    *"' does not depend on any axioms") ok=$((ok + 1)) ;;
    *"' depends on axioms: ["*"]")
      axs=$(printf '%s' "$line" | sed -e 's/.*depends on axioms: \[//' -e 's/\]$//' | tr ',' '\n' | sed 's/^ *//; s/ *$//')
      extra=$(printf '%s\n' "$axs" | grep -vxE 'propext|Classical\.choice|Quot\.sound|' || true)
      if [ -z "$extra" ]; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "$line"; fi ;;
    *error*) bad=$((bad + 1)); echo "$line" ;;
  esac
done < "$LOGS/axioms.log"
echo "results checked: $ok of $expected"
if [ "$rc" -ne 0 ] || [ "$bad" -gt 0 ] || [ "$ok" -ne "$expected" ]; then
  echo "FAILED: axiom check"; echo "Verification FAILED."; exit 1
fi
echo "Verification passed: everything builds, and every result depends only on propext, Classical.choice and Quot.sound."
