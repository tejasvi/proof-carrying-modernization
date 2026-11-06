#!/bin/bash
# initptr_checks.sh OUT: plain INITIALIZE of identifiers with POINTER items (initrepl_cases/ptr*.cob), checked
# against the lines IBM's rule 1a gives (a pointer is not a MOVE receiver; GnuCOBOL cannot be compared: its
# pointer has 8 bytes, the model's 4). Uses the front end at $COBOLFE (default: this tree's) and this tree's
# cobolrun. Writes only OUT (new). One PASS / FAIL line per check; exit status 0 only when all pass.
set -u
OUT=${1:?out dir}
T="$(cd "$(dirname "$0")/../.." && pwd)"
FE=${COBOLFE:-$T/tools/cobolfe/cobolfe.py}
C=$T/tools/difftest/initrepl_cases
RUN=$T/.lake/build/bin/cobolrun
[ -e "$OUT" ] && { echo "exists: $OUT"; exit 2; }
mkdir -p "$OUT" || exit 2
fails=0
check() { if [ "$2" = 0 ]; then echo "PASS $1"; else echo "FAIL $1"; fails=$((fails + 1)); fi; }
run() { # name: front end + cobolrun on initrepl_cases/name.cob; OUT/name.run = DISPLAY lines, then the signal
    python3 -I -B "$FE" "$C/$1.cob" --profile gnucobol --main -o "$OUT/$1.json" > "$OUT/$1.out" 2> "$OUT/$1.err"
    echo $? > "$OUT/$1.rc"
    if [ -s "$OUT/$1.json" ]; then
        "$RUN" "$OUT/$1.json" | jq -r '(.out[] | select(.display) | .display | implode), .signal' > "$OUT/$1.run" 2>&1
    fi
}
run ptr1
check "K1 ptr1: the pointer is kept by plain INITIALIZE and by REPLACING" \
    "$(printf 'P KEPT\nX [ ]\nP KEPT\nX [Z]\nstop:Cobol.StopKind.run\n' | cmp -s - "$OUT/ptr1.run"; echo $?)"
run ptr2
check "K2 ptr2: G1, G2 lowered (pointers kept, AE edited), G3 by the resolver, REPLACING, INITIALIZE of a pointer unsupported" \
    "$(printf '%s\n' 'G1 [####     / 00#### #### ]' 'G2 [   0 ####]' 'G3 [      ]' 'G1 [####Q  ####07####Q####Q]' \
        'fault:Cobol.Fault.unsupported "INITIALIZE (line 46): INITIALIZE of a pointer"' | cmp -s - "$OUT/ptr2.run"; echo $?)"
check "K3 ptr2: exactly one INITIALIZE left for the resolver (G3's)" \
    "$([ "$(jq '[.. | objects | select(has("initialize"))] | length' "$OUT/ptr2.json")" = 1 ] && \
       [ "$(jq -c '[.. | objects | select(has("initialize")) | .initialize.dsts[].item]' "$OUT/ptr2.json")" = \
         "$(jq -c '[.data[] | select(.name == "G3") | .id]' "$OUT/ptr2.json")" ]; echo $?)"
run ptr3
check "K4 ptr3: INITIALIZE ... REPLACING of a condition name is a named unsupported statement" \
    "$(command grep -qF 'INITIALIZE (line 11): INITIALIZE ... REPLACING of a condition name or an index name' "$OUT/ptr3.err"; echo $?)"
echo "pointer checks: $fails failed"
[ $fails = 0 ]
