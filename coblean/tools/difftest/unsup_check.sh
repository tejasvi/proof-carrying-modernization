#!/bin/bash
# unsup_check.sh OUT : the cases of tools/difftest/unsup_cases, each a small program with one construct
# that the front end must not drop silently. The first line of each case says what must happen:
#   EXPECT-FAULT: text   the front end accepts it and the program faults at its first statement with
#                        `unsupported "program: ... text ..."` (nothing is displayed before)
#   EXPECT-REJECT: text  the front end rejects it with a message containing text
#   EXPECT-RUN           control: no unsupported construct; the program displays START first and stops
# A line `MODE: sub` extracts the case as a called program (--sub). Prints one line per case and
# "N cases, M pass"; exit status 0 when all pass.
C="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:?output directory}"
mkdir -p "$OUT" || exit 2
n=0; ok=0
for f in "$C"/tools/difftest/unsup_cases/*.cob; do
  b=$(basename "$f" .cob)
  n=$((n + 1))
  exp=$(head -1 "$f" | sed 's/^      \* //')
  mode=--main
  command grep -q '^      \* MODE: sub' "$f" && mode=--sub
  python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$f" --profile gnucobol $mode -o "$OUT/$b.json" 2> "$OUT/$b.err"
  rc=$?
  verdict=FAIL
  if [ "${exp%%:*}" = EXPECT-REJECT ]; then
    want="${exp#EXPECT-REJECT: }"
    if [ $rc != 0 ] && command grep -qF -- "$want" "$OUT/$b.err"; then verdict=PASS; fi
    got="front end rc $rc: $(tail -1 "$OUT/$b.err")"
  elif [ $rc != 0 ]; then
    got="front end rc $rc: $(tail -1 "$OUT/$b.err")"
  else
    "$C/.lake/build/bin/cobolrun" "$OUT/$b.json" > "$OUT/$b.run.json" 2> "$OUT/$b.run.err"
    got=$(python3 -I -B -c '
import json, sys
r = json.load(open(sys.argv[1]))
d = [bytes(e["display"]).decode(errors="replace") for e in r["out"] if "display" in e]
print(len(r["out"]), d[0] if d else "-", r["signal"], sep="\t")' "$OUT/$b.run.json" 2>&1)
    IFS=$'\t' read -r nev first sig <<< "$got"
    if [ "${exp%%:*}" = EXPECT-FAULT ]; then
      want="${exp#EXPECT-FAULT: }"
      case "$sig" in
        'fault:Cobol.Fault.unsupported "program: '*)
          [ "$nev" = 0 ] && printf '%s' "$sig" | command grep -qF -- "$want" && verdict=PASS ;;
      esac
    elif [ "$exp" = EXPECT-RUN ]; then
      case "$sig" in
        stop:*) [ "$first" = START ] && ! command grep -q unsupported "$OUT/$b.err" && verdict=PASS ;;
      esac
    fi
    got="events $nev, first display '$first', signal $sig"
  fi
  [ $verdict = PASS ] && ok=$((ok + 1))
  echo "$verdict $b: $got"
done
echo "$n cases, $ok pass"
[ "$ok" = "$n" ]
