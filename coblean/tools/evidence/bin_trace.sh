#!/bin/bash
# The three TRUNC(BIN) mismatches of the random test (difftest.py --trunc bin --n 200 --seed 12,
# cases 101, 130 and 197; programs in tools/difftest/bin_cases/T00101.cob, T00130.cob, T00197.cob).
# Case 130 shows only in the per-statement outcome trace (OTRACE); t130x.cob is a minimal
# GnuCOBOL reproduction. The *_trace.cob copies DISPLAY the numeric items after each statement
# (130: also the SIZE ERROR phrase that ran); this script runs them under GnuCOBOL (TRUNC(BIN)
# flags) and under the front end + cobolrun, and prints, per case, what GnuCOBOL shows and the
# final value of the receiving item (130: the phrase that ran) in both engines.
# usage: C=<snapshot root> OUT=<scratch dir> $C/tools/evidence/bin_trace.sh
set -u
: "${C:?}" "${OUT:?}"
W=$OUT/bintrace; mkdir -p "$W/tmp" && cd "$W" || exit 2
export TMPDIR=$W/tmp
for c in 00101 00130 00197; do
  cp "$C/tools/difftest/bin_cases/t${c}_trace.cob" t$c.cob
  "$C/scripts/cobc.sh" -x -std=ibm -fno-arithmetic-osvs -o t$c t$c.cob > /dev/null 2>&1
  LD_LIBRARY_PATH=$C/third_party/gnucobol/usr/lib/x86_64-linux-gnu ./t$c | /usr/bin/grep '^S' > g$c.txt
  python3 -I -B "$C/tools/cobolfe/cobolfe.py" t$c.cob --profile gnucobol --trunc bin -o t$c.json 2> /dev/null
  "$C/.lake/build/bin/cobolrun" t$c.json > l$c.json
  jq -r '.out[] | select(.display) | .display | implode' l$c.json | /usr/bin/grep '^S' > l$c.txt
done
# 101: N2 (S9(5)V9(3) COMP-5) after SUBTRACT N4 FROM N2 (5th trace line); final N4 (last line, 2nd field)
g2=$(sed -n 5p g00101.txt | cut -d'|' -f1); g4=$(tail -n 1 g00101.txt | cut -d'|' -f2); l4=$(tail -n 1 l00101.txt | cut -d'|' -f2)
# 130: N5 (S9(1) COMP) after MOVE 1999.28 TO N5 (2nd line, 2nd field); the phrase of ADD N5 TO N6 N4
# (3rd line); N6 (S9(2)V9(1) COMP-3) and N4 after the ADD (4th line, 3rd and 1st fields)
k5=$(sed -n 2p g00130.txt | cut -d'|' -f2); kp=$(sed -n 3p g00130.txt); mp=$(sed -n 3p l00130.txt)
k6=$(sed -n 4p g00130.txt | cut -d'|' -f3); m6=$(sed -n 4p l00130.txt | cut -d'|' -f3)
k4=$(sed -n 4p g00130.txt | cut -d'|' -f1); m4=$(sed -n 4p l00130.txt | cut -d'|' -f1)
# 197: N2 (S9(6)V9(1) COMP-5) after MULTIPLY N2 BY N2 (3rd trace line); final N5 (last line, 2nd field)
h2=$(sed -n 3p g00197.txt | cut -d'|' -f1); h5=$(tail -n 1 g00197.txt | cut -d'|' -f2); m5=$(tail -n 1 l00197.txt | cut -d'|' -f2)
echo "101: GnuCOBOL shows N2=${g2#S}, final N4 GnuCOBOL=$g4 model=$l4 | 130: GnuCOBOL shows N5=$k5; ADD N5 TO N6 N4: GnuCOBOL ${kp#S}, N6=$k6, N4=${k4#S}; model ${mp#S}, N6=$m6, N4=${m4#S} | 197: GnuCOBOL shows N2=${h2#S}, final N5 GnuCOBOL=$h5 model=$m5"
