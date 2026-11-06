#!/bin/bash
# CBSTM03A + CBSTM03B against GnuCOBOL on CardDemo's sample data (tools/difftest/stm_*): the
# linked IR in ASCII (front end --profile gnucobol) and the inputs converted from code page 037
# run under cobolrun; GnuCOBOL compiles the unmodified CBSTM03B and CBSTM03A without lines
# 266-291 (the z/OS control-block walk). stm_compare.py compares both output files record by
# record, the DISPLAY lines after the walk, the walk's DISPLAY lines with the lines that follow
# from the constructed address space (t4as.json), and GnuCOBOL's exit status with the model's
# RETURN-CODE. Prints stm_compare.py's verdict lines on one line.
# Every run works in a new directory under $OUT (nothing is removed); any failing step stops
# the script with a message (set -euo pipefail).
# usage: C=<snapshot root> OUT=<scratch dir> CD=<CardDemo root> $C/tools/evidence/stm_check.sh
set -euo pipefail
: "${C:?}" "${OUT:?}" "${CD:?}"
D=$CD/app/data/EBCDIC
mkdir -p "$OUT/tmp"
W=$(mktemp -d "$OUT/stm.XXXXXX")
cd "$W"
export TMPDIR=$OUT/tmp
py() { python3 -I -B "$@"; }
fail() { echo "stm_check: $*"; exit 1; }
py "$C/tools/coverage/carddemo_inputs.py" t2.json 1:350:$D/AWS.M2.CARDDEMO.DALYTRAN.PS \
  3:50:$D/AWS.M2.CARDDEMO.CARDXREF.PS 5:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS \
  6:50:$D/AWS.M2.CARDDEMO.TCATBALF.PS > /dev/null
"$C/.lake/build/bin/cobolrun" "$C/examples/carddemo/cbtrn02c.ir.json" --inputs t2.json \
  --clock 2025102414300000-0500 > t2.out.json
py "$C/tools/coverage/creastmt_inputs.py" t2.out.json "$D" t4.json t4as.json > /dev/null
py "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBSTM03A.CBL" -I "$CD/app/cpy" --tab-width 4 --profile gnucobol -o a_ascii.json
py "$C/tools/cobolfe/cobolfe.py" "$CD/app/cbl/CBSTM03B.CBL" -I "$CD/app/cpy" --tab-width 4 --profile gnucobol -o b_ascii.json
py "$C/tools/cobolfe/link.py" a_ascii.json b_ascii.json -o ab_ascii.json > /dev/null
mkdir g
py "$C/tools/difftest/stm_ascii.py" ab_ascii.json t4.json g > /dev/null
CD=$CD bash "$C/tools/difftest/stm_gnucobol.sh" g > g/gnucobol.log 2>&1 \
  || fail "stm_gnucobol.sh failed: $(tail -1 g/gnucobol.log)"
[ -s g/gnucobol_rc.txt ] || fail "stm_gnucobol.sh wrote no exit status"
"$C/.lake/build/bin/cobolrun" g/ir_ascii.json --inputs g/inputs_ascii.json --addrspace t4as.json > g/ours.json
rc=0
py "$C/tools/difftest/stm_compare.py" g/ours.json g --addrspace t4as.json > g/compare.txt || rc=$?
tr '\n' ' ' < g/compare.txt; echo
exit $rc
