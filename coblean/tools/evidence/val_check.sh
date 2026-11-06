#!/bin/bash
# val_check.sh N RC LOG RESULTS : the value of a validation row. Prints the tally of RESULTS (one
# {"case", "status"} per line) followed by "N cases, tester exit RC" when the tester exited
# normally (status 0 = every case ok, 1 = some other status; no Python traceback in LOG) and
# RESULTS holds exactly the cases 0 .. N-1, once each. Otherwise prints "FAIL: reason" and exits 1.
set -u
n="${1:?N}"; rc="${2:?tester exit status}"; log="${3:?log}"; res="${4:?results.jsonl}"
fail() { echo "FAIL: $*"; exit 1; }
case "$rc" in 0|1) ;; *) fail "tester exit status $rc" ;; esac
[ -f "$log" ] || fail "no log $log"
if command grep -q '^Traceback' "$log"; then fail "Python traceback in $log"; fi
[ -f "$res" ] || fail "no results $res"
cases=$(jq -r '.case' "$res" | LC_ALL=C sort -n --parallel=1 | tr '\n' ' ')
want=$(seq 0 $((n - 1)) | tr '\n' ' ')
[ "$cases" = "$want" ] || fail "cases are not exactly 0..$((n - 1)) ($(jq -s length "$res") records)"
echo "$(jq -s -c 'group_by(.status) | map({(.[0].status): length}) | add' "$res") $n cases, tester exit $rc"
