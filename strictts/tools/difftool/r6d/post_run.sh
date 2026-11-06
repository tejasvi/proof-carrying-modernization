#!/bin/bash
# After a run chain (R6d; R6c's post_run.sh with an optional single recheck lane): freeze the Lean
# confirmation files, replay every counterexample in plain node, type-check every counterexample call,
# write the per-pair table, then recheck every collected Lean batch file with `lake env lean` (two
# lanes, or one with LANES=1) and verify axioms and errors.
#   [LANES=1] bash scratch/r6d/post_run.sh RUN_DIR PAIRS_ROOT FROM_STAMP TABLE_NAME DRAFT_NAME
#   e.g. bash scratch/r6d/post_run.sh scratch/r6d/es /home/user/strictts/scratch/hist_es 20261027T070241Z r6d_table.tsv R6D_draft.md
set -u
cd /home/user/strictts_ws/r6d
D=${1:?run dir}; P=${2:?pairs root}; FROM=${3:?from stamp}; TN=${4:?table name}; DN=${5:?draft name}
LOG=$D/post.log
say() { echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $*" >> "$LOG"; }
say "start: HEAD $(git rev-parse HEAD) dist sha $(cat tools/difftool/dist/*.js | sha256sum | cut -c1-16)"
tools/run.sh 0.05 300 node $D/collect_confirm.js scratch/difftool "$FROM" $D/evidence_confirm >> "$LOG" 2>&1
say "collect_confirm rc=$?"
tools/run.sh 0.3 590 node $D/cex_replay_v2.js $D/chunks "$P" $D/replay_v2 >> "$LOG" 2>&1
say "replay rc=$?"
tools/run.sh 0.3 590 node $D/tscheck_cex.js $D/chunks "$P" $D/tscheck_work > $D/tscheck.tsv 2> $D/tscheck.err
say "tscheck rc=$?"
TABLE_NAME=$TN DRAFT_NAME=$DN tools/run.sh 0.05 120 node $D/report.js $D "$P" >> "$LOG" 2>&1
say "report rc=$?"
E=$D/evidence
ls $E/*.lean > $D/recheck_files.txt
one() { tools/run.sh 0.5 590 lake env lean --tstack=262144 "$1" > "${1%.lean}.recheck.out" 2>&1; say "$(basename "$1") rc=$?"; }
lane() { local i=0; while read -r f; do i=$((i + 1)); [ $((i % 2)) -eq $1 ] && one "$f"; done < $D/recheck_files.txt; }
# LANES=1: one recheck at a time (while another run holds two cores)
if [ "${LANES:-2}" = 1 ]; then while read -r f; do one "$f"; done < $D/recheck_files.txt
else
  lane 1 & P1=$!
  lane 0 & P2=$!
  wait $P1 $P2
fi
tools/run.sh 0.05 120 node /home/user/strictts_ws/rally/scratch/r6/recheck_verify_v2.js $E >> "$LOG" 2>&1
say "verify rc=$?"
say "POST DONE"
