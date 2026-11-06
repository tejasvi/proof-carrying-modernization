#!/bin/bash
# One CardDemo program through the front end and the Lean resolver; prints one line:
#   NAME kind=<batch|cics|ims|db2|mq joined by +> lines=<non-comment lines> fe=<ok|stop> \
#     unsupported=<n> resolves=<yes|no> signal=<cobolrun outcome with no input files>
# kind comes from the source text: EXEC CICS -> cics, EXEC DLI / CBLTDLI -> ims, EXEC SQL -> db2,
# CALL 'MQ...' -> mq, none of these -> batch. lines: tools/evidence/cobol_lines.awk.
# Copybooks: the program's own cpy and cpy-bms directories, then app/cpy and app/cpy-bms.
# usage: C=<snapshot root> OUT=<scratch dir> CD=<CardDemo root> $C/tools/evidence/cov_one.sh PROGRAM.cbl
set -u
: "${C:?}" "${OUT:?}" "${CD:?}"
p="$1"; d=$(dirname "$p"); n=$(basename "$p"); n=${n%.*}
mkdir -p "$OUT/fe"
kind=""
/usr/bin/grep -q -i 'EXEC  *CICS' "$p" && kind="$kind+cics"
/usr/bin/grep -q -i -E 'EXEC  *DLI|CBLTDLI' "$p" && kind="$kind+ims"
/usr/bin/grep -q -i 'EXEC  *SQL' "$p" && kind="$kind+db2"
/usr/bin/grep -q -i -E "CALL +'MQ" "$p" && kind="$kind+mq"
[ -z "$kind" ] && kind="+batch"
lines=$(awk -f "$C/tools/evidence/cobol_lines.awk" "$p")
inc=()
for c in "$d/../cpy" "$d/../cpy-bms" "$CD/app/cpy" "$CD/app/cpy-bms"; do
  [ -d "$c" ] && inc+=(-I "$(cd "$c" && pwd)")
done
inc=($(printf '%s\n' "${inc[@]}" | awk 'NR % 2 == 0 && !seen[$0]++ { print "-I"; print }'))
if python3 -I -B "$C/tools/cobolfe/cobolfe.py" "$p" "${inc[@]}" --tab-width 4 --report \
    -o "$OUT/fe/$n.json" > "$OUT/fe/$n.report.json" 2> "$OUT/fe/$n.err"; then
  u=$(jq '.unsupported | length' "$OUT/fe/$n.report.json")
  if "$C/.lake/build/bin/cobolrun" "$OUT/fe/$n.json" > "$OUT/fe/$n.run.json" 2> "$OUT/fe/$n.run.err"; then
    s=$(jq -r '.signal' "$OUT/fe/$n.run.json")
    echo "$n kind=${kind#+} lines=$lines fe=ok unsupported=$u resolves=yes signal=$s"
  else
    echo "$n kind=${kind#+} lines=$lines fe=ok unsupported=$u resolves=no reason=\"$(head -c 120 "$OUT/fe/$n.run.err" | tr '\n' ' ')\""
  fi
else
  r=$(sed -e 's|^cobolfe: [^ ]*/||' -e 's| in \[.*$||' "$OUT/fe/$n.err" | head -n 1 | head -c 120)
  echo "$n kind=${kind#+} lines=$lines fe=stop reason=\"$r\""
fi
