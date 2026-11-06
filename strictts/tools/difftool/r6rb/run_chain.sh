#!/bin/bash
# R6 full run: every pair of the frozen testable list (both scan directories) through `strictts-diff
# history --phase run`, in chunks of at most 30 pairs (one guarded job each, under 10 minutes), two
# lanes at a time. Each chunk writes its own JSON and log; a chunk that ends without its JSON is
# retried once, pair by pair. Then the Lean batch files the proofs name are copied into evidence/.
#   bash scratch/r6rb/run_chain.sh   (R6rb: R6r frozen pairs, const-arrow tool; private no-checkout clone of the R6r clone)
set -u
cd /home/user/strictts_ws/constarrow
R6=scratch/r6rb
H=/home/user/strictts/scratch/hist_remeda
REPO=/home/user/strictts_ws/constarrow/scratch/rescan/clone_remeda
LOG=$R6/run_chain.log
say() { echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $*" >> "$LOG"; }
mkdir -p $R6/chunks
say "start: HEAD $(git rev-parse HEAD) dist sha $(cat tools/difftool/dist/*.js | sha256sum | cut -c1-16)"

# chunk lists: <dir> <id...>, from the frozen testable list (lines "<dir>/<id>")
rm -f $R6/chunks/list_*
awk -F/ '{print $1, $2}' $R6/r7_testable.txt | sort | awk -v d=$R6/chunks '
  { if ($1 != cur || n == 30) { k++; n = 0; cur = $1; f = sprintf("%s/list_%03d__%s", d, k, $1) } print $2 > f; n++ }'
ls $R6/chunks/list_* > $R6/chunks/all_lists.txt
say "chunks: $(wc -l < $R6/chunks/all_lists.txt)"

run_chunk() {  # list file
  local L=$1 b dir re
  b=$(basename "$L"); dir=${b#*__}
  re="^($(paste -sd'|' "$L"))\$"
  tools/run.sh 1.0 590 node tools/difftool/dist/cli.js history --repo $REPO --out $H/$dir --phase run --only "$re" \
    --json $R6/chunks/$b.json > $R6/chunks/$b.log 2>&1
  local rc=$?
  if [ ! -s $R6/chunks/$b.json ]; then
    say "$b rc=$rc without JSON: retry pair by pair"
    while read -r id; do
      tools/run.sh 0.5 590 node tools/difftool/dist/cli.js history --repo $REPO --out $H/$dir --phase run --only "^${id}\$" \
        --json $R6/chunks/${b}_$id.json > $R6/chunks/${b}_$id.log 2>&1
      say "$b/$id rc=$?"
    done < "$L"
  else
    say "$b rc=$rc $(tail -n 1 $R6/chunks/$b.log)"
  fi
}

# two lanes: odd and even chunks
lane() { local i=0; while read -r L; do i=$((i + 1)); [ $((i % 2)) -eq $1 ] && run_chunk "$L"; done < $R6/chunks/all_lists.txt; }
lane 1 & P1=$!
lane 0 & P2=$!
wait $P1 $P2
say "runs done"

# evidence: the Lean batch files (and their outputs) that the proofs and confirmations name
mkdir -p $R6/evidence
tools/run.sh 0.05 300 node /home/user/strictts_ws/rally/scratch/r6/collect.js $R6/chunks $R6/evidence >> "$LOG" 2>&1
say "collect rc=$?"
say "CHAIN DONE"
