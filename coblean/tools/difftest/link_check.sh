#!/bin/bash
# link_check.sh OUT : the linked-program cases of tools/difftest/link_cases, run by GnuCOBOL (callees with
# cobc -m) and by the front end + tools/cobolfe/link.py + cobolrun; the DISPLAY output of the two must agree.
#   ZW101A + ZW102A          the callee returns by EXIT PROGRAM (linked as GOBACK)
#   ZS101A + ZS102A          caller and callee have sections with the same names
#   ZN101A + ZN102A + ZN103A a callee that calls another program (nested local call)
# Prints one line per case and "N cases, M agree"; exit status 0 when all agree.
C="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:?output directory}"
LIB="$C/third_party/gnucobol/usr/lib/x86_64-linux-gnu"
FLAGS="-std=ibm -fbinary-truncate -fno-arithmetic-osvs"
mkdir -p "$OUT" || exit 2
cp "$C"/tools/difftest/link_cases/*.cob "$OUT"/ || exit 2
cd "$OUT" || exit 2
n=0; ok=0
run_case() {  # MAIN SUB...  (each SUB calls the next one)
  local M="$1"; shift
  local s g m cur i
  n=$((n + 1))
  for s in "$@"; do "$C/scripts/cobc.sh" -m $FLAGS -o "$s.so" "$s.cob" > "$s.cobc.txt" 2>&1 || { echo "$M: cobc -m $s failed"; return; }; done
  "$C/scripts/cobc.sh" -x $FLAGS -o "$M.exe" "$M.cob" > "$M.cobc.txt" 2>&1 || { echo "$M: cobc -x failed"; return; }
  g=$(COB_LIBRARY_PATH="$OUT" LD_LIBRARY_PATH="$LIB" timeout 20 "./$M.exe" 2>&1)
  python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$M.cob" --profile gnucobol --main -o "$M.json" || { echo "$M: front end failed"; return; }
  for s in "$@"; do python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$s.cob" --profile gnucobol --sub -o "$s.json" || { echo "$M: front end failed on $s"; return; }; done
  cur=""
  for ((i = $#; i >= 1; i--)); do
    s="${!i}"
    if [ -n "$cur" ]; then
      python3 -I -B "$C/tools/cobolfe/link.py" "$s.json" "$cur" -o "$s.linked.json" > /dev/null || { echo "$M: link failed"; return; }
      cur="$s.linked.json"
    else
      cur="$s.json"
    fi
  done
  python3 -I -B "$C/tools/cobolfe/link.py" "$M.json" "$cur" -o "$M.linked.json" > /dev/null || { echo "$M: link failed"; return; }
  m=$(timeout 60 "$C/.lake/build/bin/cobolrun" "$M.linked.json" --fuel 1000000 | python3 -I -B -c '
import json, sys
r = json.loads(sys.stdin.read())
for e in r["out"]:
    if "display" in e:
        print(bytes(e["display"]).decode(errors="replace"))
print("signal", r["signal"])')
  if [ "$g" = "$(printf '%s\n' "$m" | sed '$d')" ] && [ "$(printf '%s\n' "$m" | tail -1)" = "signal stop:Cobol.StopKind.run" ]; then
    ok=$((ok + 1)); echo "$M: agree: $(echo $g)"
  else
    echo "$M: DIFFER: GnuCOBOL [$(echo $g)] model [$(echo $m)]"
  fi
}
run_case ZW101A ZW102A
run_case ZS101A ZS102A
run_case ZN101A ZN102A ZN103A
echo "$n cases, $ok agree"
[ "$ok" = "$n" ]
