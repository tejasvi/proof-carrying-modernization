#!/bin/bash
# Run CardDemo batch programs on CardDemo's own sample data (app/data/EBCDIC) with cobolrun and
# print one summary line: end signal and event counts. The commands are those of
# examples/carddemo/README.md; everything is written under $OUT.
# usage: C=<snapshot root> OUT=<scratch dir> CD=<CardDemo root> $C/tools/evidence/sample_runs.sh PROG
#   PROG: cbtrn02c | cbtrn03c | cbact01c | cbstm03ab | cbact04c
set -u
: "${C:?}" "${OUT:?}" "${CD:?}"
D=$CD/app/data/EBCDIC
R=$C/.lake/build/bin/cobolrun
mkdir -p "$OUT/sample" && cd "$OUT/sample" || exit 2
py() { python3 -I -B "$@"; }
summary() {  # end signal, events, displays, writes per file, rewrites
  jq -r '"signal=\(.signal) events=\(.out | length) displays=\([.out[] | select(.display)] | length) writes=\([.out[] | select(.write) | .write.file] | group_by(.) | map("\(.[0]):\(length)") | join(",")) rewrites=\([.out[] | select(.rewrite)] | length)"' "$1"
}
t2() {
  py "$C/tools/coverage/carddemo_inputs.py" t2.json 1:350:$D/AWS.M2.CARDDEMO.DALYTRAN.PS \
    3:50:$D/AWS.M2.CARDDEMO.CARDXREF.PS 5:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS \
    6:50:$D/AWS.M2.CARDDEMO.TCATBALF.PS > /dev/null
  "$R" "$C/examples/carddemo/cbtrn02c.ir.json" --inputs t2.json --clock 2025102414300000-0500 > t2.out.json
}
case "$1" in
  cbtrn02c)
    t2; echo "$(summary t2.out.json) return-code=$(jq -r '.mem[3250] * 256 + .mem[3251]' t2.out.json)" ;;
  cbtrn03c)
    t2
    py "$C/tools/coverage/tranrept_inputs.py" t2.out.json 2025-10-01 2025-10-31 "$D" t3.json > /dev/null
    "$R" "$C/examples/carddemo/cbtrn03c.ir.json" --inputs t3.json > t3.out.json; summary t3.out.json ;;
  cbact01c)
    py "$C/tools/coverage/carddemo_inputs.py" t1.json 1:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS > /dev/null
    "$R" "$C/examples/carddemo/cbact01c.ir.json" --inputs t1.json --externals carddemo > t1.out.json
    summary t1.out.json ;;
  cbstm03ab)
    t2
    py "$C/tools/coverage/creastmt_inputs.py" t2.out.json "$D" t4.json t4as.json > /dev/null
    "$R" "$C/examples/carddemo/cbstm03ab.ir.json" --inputs t4.json --addrspace t4as.json > t4.out.json
    summary t4.out.json ;;
  cbact04c)  # plus the number of DISPLAYs of 'TRY WITH DEFAULT GROUP CODE' (code page 037)
    py "$C/tools/coverage/carddemo_inputs.py" t5.json 1:50:$D/AWS.M2.CARDDEMO.TCATBALF.PS \
      2:50:$D/AWS.M2.CARDDEMO.CARDXREF.PS 3:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS \
      4:50:$D/AWS.M2.CARDDEMO.DISCGRP.PS > /dev/null
    "$R" "$C/examples/carddemo/cbact04c.ir.json" --inputs t5.json --clock 2025102414300000-0500 > t5.out.json
    msg=$(py -c 'print(list("TRY WITH DEFAULT GROUP CODE".encode("cp037")))')
    echo "$(summary t5.out.json) default-group-retries=$(jq --argjson m "$msg" '[.out[] | select(.display == $m)] | length' t5.out.json)" ;;
  *) echo "unknown program $1"; exit 2 ;;
esac
