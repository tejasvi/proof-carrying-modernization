#!/usr/bin/env bash
# Lean elaboration of emitted modules, one guarded job each (tools/run.sh, under 10 minutes):
#   tests/coverage/elab.sh tests/coverage/lean/X.lean ...
# prints: module, lines, bytes, exit code, wall seconds, number of error lines (log in X.elab.log)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
for f in "$@"; do
  log="${f%.lean}.elab.log"
  t0=$(date +%s.%N)
  ( cd "$ROOT" && "$ROOT/tools/run.sh" 0.3 590 lake env lean -DElab.async=false "$f" ) > "$log" 2>&1
  rc=$?
  t1=$(date +%s.%N)
  printf '%s lines=%s bytes=%s rc=%s secs=%.1f errors=%s\n' "$(basename "$f")" "$(wc -l < "$f")" "$(wc -c < "$f")" "$rc" \
    "$(echo "$t1 - $t0" | bc)" "$(grep -c ': error' "$log")"
done
