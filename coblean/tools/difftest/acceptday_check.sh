#!/bin/bash
# acceptday_check.sh OUT : ACCEPT FROM DAY (YYDDD), DAY YYYYDDD and DAY-OF-WEEK, on
# tools/difftest/accept_cases/acceptday1.cob:
#  1. GnuCOBOL (-std=ibm, its own clock): the five C lines are Y (the values agree with DATE YYYYMMDD
#     of the same run by INTEGER-OF-DATE, in numeric and alphanumeric receivers);
#  2. the model (front end + cobolrun --clock) at four clock readings (the end of a leap year, a
#     century leap day, a Monday, 2026-10-27): the five C lines are Y, the V line holds the values
#     date(1) gives for that date, and the run ends normally.
# Prints one line per check and "acceptday checks: N failed"; exit status 0 when none failed.
C="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:?output directory}"
mkdir -p "$OUT" || exit 2
P=$C/tools/difftest/accept_cases/acceptday1.cob
fail=0
if "$C/scripts/cobc.sh" -x -std=ibm -o "$OUT/acceptday1" "$P" > "$OUT/cobc.txt" 2>&1; then
  LD_LIBRARY_PATH="$C/third_party/gnucobol/usr/lib/x86_64-linux-gnu" "$OUT/acceptday1" > "$OUT/gc.out" 2>&1
  rc=$?
  nc=$(awk '/^C[1-5] Y$/ {n++} END {print n + 0}' "$OUT/gc.out")
  if [ "$rc" = 0 ] && [ "$nc" = 5 ]; then
    echo "PASS GnuCOBOL: 5 of 5 C lines Y, $(awk '/^V / {print}' "$OUT/gc.out")"
  else
    echo "FAIL GnuCOBOL: exit status $rc, $nc of 5 C lines Y"; fail=$((fail + 1))
  fi
else
  echo "FAIL cobc (see $OUT/cobc.txt)"; fail=$((fail + 1))
fi
if ! python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$P" --profile gnucobol --main -o "$OUT/acceptday1.json" \
    2> "$OUT/fe.err" || command grep -q unsupported "$OUT/fe.err"; then
  echo "FAIL front end (see $OUT/fe.err)"; fail=$((fail + 1))
fi
for d in 2024-12-31 2000-02-29 2001-01-01 2026-10-27; do
  set -- $(date -u -d "$d" +'%y%j %Y%j %u')
  want="V $1 $2 $3 $1|$3|"
  "$C/.lake/build/bin/cobolrun" "$OUT/acceptday1.json" --clock "$(echo "$d" | tr -d -)1200000000+0000" \
      > "$OUT/model_$d.json" 2> "$OUT/model_$d.err"
  sig=$(jq -r '.signal' "$OUT/model_$d.json" 2>/dev/null)
  jq -r '.out[] | select(.display) | .display | implode' "$OUT/model_$d.json" > "$OUT/model_$d.txt" 2>/dev/null
  nc=$(awk '/^C[1-5] Y$/ {n++} END {print n + 0}' "$OUT/model_$d.txt")
  got=$(awk '/^V / {print}' "$OUT/model_$d.txt")
  if [ "${sig%%:*}" = stop ] && [ "$nc" = 5 ] && [ "$got" = "$want" ]; then
    echo "PASS model $d: 5 of 5 C lines Y, $got"
  else
    echo "FAIL model $d: signal $sig, $nc of 5 C lines Y, '$got' (date(1): '$want')"; fail=$((fail + 1))
  fi
done
echo "acceptday checks: $fail failed"
[ "$fail" = 0 ]
