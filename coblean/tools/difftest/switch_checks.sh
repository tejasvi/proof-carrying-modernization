#!/bin/bash
# switch_checks.sh OUT: the switch cases of switch_cases/ that the random tester swtest.py does not
# cover (IBM profile, GnuCOBOL's SWITCH-n names, option and environment errors, linking). Uses the
# front end at $COBOLFE (default: this tree's), cobolrun and GnuCOBOL of this tree. Writes only OUT
# (new). Prints one PASS / FAIL line per check; exit status 0 only when all pass.
set -u
OUT=${1:?out dir}
T="$(cd "$(dirname "$0")/../.." && pwd)"
FE=${COBOLFE:-$T/tools/cobolfe/cobolfe.py}
LINK=$(dirname "$FE")/link.py
C=$T/tools/difftest/switch_cases
RUN=$T/.lake/build/bin/cobolrun
[ -e "$OUT" ] && { echo "exists: $OUT"; exit 2; }
mkdir -p "$OUT" || exit 2
fails=0
check() { # name condition-result
    if [ "$2" = 0 ]; then echo "PASS $1"; else echo "FAIL $1"; fails=$((fails + 1)); fi
}
fe() { # out-name env-assignments... -- front-end args...
    local n=$1; shift
    local envs=()
    while [ "$1" != "--" ]; do envs+=("$1"); shift; done
    shift
    env -u COB_SWITCH_0 -u COB_SWITCH_1 -u COB_SWITCH_36 "${envs[@]}" python3 -I -B "$FE" "$@" \
        -o "$OUT/$n.json" > "$OUT/$n.out" 2> "$OUT/$n.err"
    echo $? > "$OUT/$n.rc"
}
val() { jq -c --arg n "$2" '.data[] | select(.name == $n) | .value.alnum.bs' "$OUT/$1.json" 2>/dev/null; }
disp() { "$RUN" "$OUT/$1.json" | jq -r '(.out[] | select(.display) | .display | implode), .signal'; }

fe c1 COB_SWITCH_0=ON -- "$C/swq1.cob" --profile ibm
check "C1 ibm profile ignores COB_SWITCH_0=ON: UPSI-0 starts off" "$([ "$(cat $OUT/c1.rc)" = 0 ] && [ "$(val c1 %UPSI-0)" = "[240]" ]; echo $?)"
fe c2 -- "$C/swq1.cob" --profile ibm --switch UPSI-0=ON
check "C2 ibm profile --switch UPSI-0=ON: starts on" "$([ "$(val c2 %UPSI-0)" = "[241]" ]; echo $?)"
fe c3 -- "$C/swq1.cob" --profile gnucobol --switch UPSI-0=ON
disp c3 > "$OUT/c3.run" 2>&1
check "C3 qualified condition (U0-ON OF U0) true, then SET TO TRUE faults unsupported" \
    "$(printf 'Q ON\nfault:Cobol.Fault.unsupported "SET (line 18): SET TO TRUE / FALSE of a switch-status condition name"\n' | cmp -s - "$OUT/c3.run"; echo $?)"
fe c4 -- "$C/swn1.cob" --profile ibm
check "C4 ibm profile: SWITCH-1 is no switch name, ON-SWITCH-1 does not resolve (rejected)" \
    "$([ "$(cat $OUT/c4.rc)" = 1 ] && command grep -q 'unknown data name ON-SWITCH-1' "$OUT/c4.err"; echo $?)"
fe c5 COB_SWITCH_1=ON COB_SWITCH_36=on -- "$C/swn1.cob" --profile gnucobol
disp c5 > "$OUT/c5.run" 2>&1
check "C5 gnucobol profile, COB_SWITCH_1=ON COB_SWITCH_36=on: SWITCH-1 and SWITCH-36 on" \
    "$([ "$(val c5 %SWITCH-1)" = "[49]" ] && [ "$(val c5 %SWITCH-36)" = "[49]" ]; echo $?)"
mkdir -p "$OUT/gc" && "$T/scripts/cobc.sh" -x -std=cobol85 -o "$OUT/gc/swn1" "$C/swn1.cob" > "$OUT/gc/cobc.txt" 2>&1
env -i PATH=/usr/bin:/bin LD_LIBRARY_PATH="$T/third_party/gnucobol/usr/lib/x86_64-linux-gnu" COB_SWITCH_1=ON \
    COB_SWITCH_36=on "$OUT/gc/swn1" > "$OUT/gc/run.txt" 2>&1
check "C5b the same DISPLAY lines as GnuCOBOL -std=cobol85 with that environment" \
    "$(head -n -1 "$OUT/c5.run" | cmp -s - "$OUT/gc/run.txt" && [ "$(tail -1 "$OUT/c5.run")" = stop:Cobol.StopKind.run ]; echo $?)"
fe c6 COB_SWITCH_1=ON -- "$C/swn1.cob" --profile gnucobol --switch SWITCH-1=OFF
check "C6 --switch SWITCH-1=OFF wins over COB_SWITCH_1=ON" "$([ "$(val c6 %SWITCH-1)" = "[48]" ]; echo $?)"
fe c7 -- "$C/swn1.cob" --profile ibm --switch SWITCH-1=ON
check "C7 ibm profile --switch SWITCH-1=ON: refused (exit 2)" "$([ "$(cat $OUT/c7.rc)" = 2 ]; echo $?)"
fe c8 COB_SWITCH_1=1 -- "$C/swn1.cob" --profile gnucobol
check "C8 COB_SWITCH_1=1: rejected (only ON or OFF)" \
    "$([ "$(cat $OUT/c8.rc)" = 1 ] && command grep -q 'COB_SWITCH_1=.1.: give ON or OFF' "$OUT/c8.err"; echo $?)"
fe c9a -- "$C/swcall1.cob" --profile ibm --main
fe c9b -- "$C/swsub1.cob" --profile ibm --sub
python3 -I -B "$LINK" "$OUT/c9a.json" "$OUT/c9b.json" -o "$OUT/c9.json" > "$OUT/c9.out" 2> "$OUT/c9.err"
rc=$?
check "C9 link.py refuses a caller and a callee that both use UPSI-0" \
    "$([ $rc != 0 ] && command grep -q 'both programs use the switch UPSI-0' "$OUT/c9.err"; echo $?)"
echo "switch checks: $fails failed"
[ $fails = 0 ]
