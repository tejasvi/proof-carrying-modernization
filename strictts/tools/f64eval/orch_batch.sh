#!/usr/bin/env bash
# usage: orch_batch.sh VARIANT OUTFILE [tests...]  -- elaborate T_<test>_<VARIANT>.lean for each test (all if none given);
# one line per test: name status seconds  (status proved = no error and no sorryAx)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
D=$ROOT/scratch/f64eval
V=$1; OUT=$2; shift 2; export ORCH=${ORCH:-orch}
if [ $# -eq 0 ]; then set -- $(ls $D/$ORCH/T_*_"$V".lean | sed "s#.*/T_##; s#_$V.lean##"); fi
: > "$OUT"
for t in "$@"; do
  f=$D/$ORCH/T_${t}_$V.lean
  s=$(date +%s.%N)
  log=$D/$ORCH/log_${t}_$V.txt
  timeout 300 $ROOT/tools/f64eval/orch_chk.sh "$f" > "$log" 2>&1
  rc=$?
  e=$(date +%s.%N)
  if [ $rc -eq 0 ] && ! grep -q "error" "$log" && ! grep -q "sorryAx" "$log"; then st=proved; else st=stuck; fi
  printf "%s %s %.1f rc=%s\n" "$t" "$st" "$(echo "$e - $s" | bc)" "$rc" >> "$OUT"
done
