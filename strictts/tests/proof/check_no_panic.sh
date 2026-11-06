#!/usr/bin/env bash
# Run the regression files whose check is that Lean prints no PANIC (e.g. "loose bvar in
# expression" from a tactic handing a term with loose bound variables to whnf); exit 1 if any does.
#   tools/run.sh 0.2 590 tests/proof/check_no_panic.sh
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
status=0
for f in tests/proof/LooseBVarRegression.lean; do
  out=$(lake env lean -DElab.async=false "$f" 2>&1)
  n=$(printf '%s\n' "$out" | grep -c 'PANIC')
  echo "$f: $n PANIC line(s)"
  [ "$n" -eq 0 ] || status=1
done
exit $status
