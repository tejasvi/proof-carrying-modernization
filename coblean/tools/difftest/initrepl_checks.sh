#!/bin/bash
# initrepl_checks.sh OUT: the INITIALIZE forms of initrepl_cases/ that stay unsupported or are
# rejected (the random tester initrepltest.py generates none of them). Uses the front end at
# $COBOLFE (default: this tree's). Writes only OUT (new). One PASS / FAIL line per check; exit
# status 0 only when all pass.
set -u
OUT=${1:?out dir}
T="$(cd "$(dirname "$0")/../.." && pwd)"
FE=${COBOLFE:-$T/tools/cobolfe/cobolfe.py}
C=$T/tools/difftest/initrepl_cases
[ -e "$OUT" ] && { echo "exists: $OUT"; exit 2; }
mkdir -p "$OUT" || exit 2
fails=0
python3 -I -B "$FE" "$C/irunsup1.cob" --profile gnucobol --main -o "$OUT/u1.json" > "$OUT/u1.out" 2> "$OUT/u1.err"
echo "irunsup1 rc=$?"
n=0
while IFS='|' read -r line what; do
    n=$((n + 1))
    if command grep -qF "INITIALIZE (line $line): $what" "$OUT/u1.err"; then echo "PASS U$n line $line: $what"
    else echo "FAIL U$n line $line: $what"; fails=$((fails + 1)); fi
done <<'LIST'
18|INITIALIZE WITH FILLER
19|INITIALIZE ... TO VALUE
20|INITIALIZE ... TO VALUE
21|INITIALIZE ... THEN TO DEFAULT
22|INITIALIZE ... THEN TO DEFAULT
23|INITIALIZE ... REPLACING of an item with a data-name subscript or reference modification
24|INITIALIZE ... REPLACING of an item with a data-name subscript or reference modification
25|INITIALIZE ... REPLACING BY an item with a data-name subscript or reference modification
26|INITIALIZE ... REPLACING BY an item with a data-name subscript or reference modification
27|INITIALIZE ... REPLACING BY an item in the storage of an identifier
28|INITIALIZE ... REPLACING of a pointer or index data item
LIST
k=$(command grep -c 'unsupported: ' "$OUT/u1.err")
if [ "$k" = 11 ] && ! command grep -q 'line 29' "$OUT/u1.err"; then echo "PASS U12 exactly 11 unsupported statements (line 29 supported)"
else echo "FAIL U12 $k unsupported lines"; fails=$((fails + 1)); fi
python3 -I -B "$FE" "$C/irbadby1.cob" --profile gnucobol --main -o "$OUT/b1.json" > "$OUT/b1.out" 2> "$OUT/b1.err"
rc=$?
if [ $rc = 1 ] && command grep -q 'REPLACING BY a group item' "$OUT/b1.err"; then echo "PASS B1 BY a group item rejected"
else echo "FAIL B1 rc=$rc"; fails=$((fails + 1)); fi
python3 -I -B "$FE" "$C/irindex2.cob" --profile gnucobol --main -o "$OUT/x2.json" > "$OUT/x2.out" 2> "$OUT/x2.err"
echo "irindex2 rc=$?"
n=0
while IFS='|' read -r line what; do
    n=$((n + 1))
    if command grep -qF "INITIALIZE (line $line): $what" "$OUT/x2.err"; then echo "PASS X$n line $line: $what"
    else echo "FAIL X$n line $line: $what"; fails=$((fails + 1)); fi
done <<'LIST'
19|INITIALIZE ... REPLACING of an index data item
20|INITIALIZE ... REPLACING of a condition name or an index name
21|INITIALIZE ... REPLACING of a condition name or an index name
LIST
echo "initialize checks: $fails failed"
[ $fails = 0 ]
