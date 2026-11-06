#!/bin/bash
# R6: check every collected Lean batch file again with `lake env lean` at the frozen commit (the
# difftool's own invocation: --tstack=262144), two at a time, then verify that every PROVED theorem
# prints exactly the standard axioms and that each recheck output equals the run's output.
#   bash scratch/r6/recheck.sh
set -u
cd /home/user/strictts_ws/rally
E=scratch/r6/evidence
LOG=scratch/r6/recheck.log
say() { echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $*" >> "$LOG"; }
say "start: HEAD $(git rev-parse HEAD)"
ls $E/*.lean > scratch/r6/recheck_files.txt
one() { tools/run.sh 0.5 590 lake env lean --tstack=262144 "$1" > "${1%.lean}.recheck.out" 2>&1; say "$(basename "$1") rc=$?"; }
lane() { local i=0; while read -r f; do i=$((i + 1)); [ $((i % 2)) -eq $1 ] && one "$f"; done < scratch/r6/recheck_files.txt; }
lane 1 & P1=$!
lane 0 & P2=$!
wait $P1 $P2
tools/run.sh 0.05 120 node scratch/r6/recheck_verify_v2.js $E >> "$LOG" 2>&1
say "verify rc=$?"
say "RECHECK DONE"
