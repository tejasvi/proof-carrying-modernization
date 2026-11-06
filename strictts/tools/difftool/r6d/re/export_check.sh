#!/bin/bash
# R6rb (R6r script, grep without a pipe: a pipe into grep -q could end the writer early, and pipefail
# then read a match as none): is the function of each refuted pair exported by its module, in the original source of both
# versions (git show from the no-checkout remeda clone; the run's slices add an export for the target,
# so they cannot answer this)? Writes scratch/r7/refuted_export.tsv (pair, function, file, old, new).
#   bash scratch/r6d/re/export_check.sh   (OUT, TSCHECK override the output and input)
set -euo pipefail
cd /home/user/strictts_ws/r6d
R=/home/user/strictts_ws/constarrow/scratch/rescan/clone_remeda
OUT=${OUT:-scratch/r6d/re/refuted_export.tsv}
printf 'pair\tfunction\tfile\told\tnew\n' > "$OUT"
awk -F'\t' 'NR>1 {print $1}' ${TSCHECK:-scratch/r6d/re/tscheck.tsv} | sort --parallel=1 -u |
while read -r id; do
  read -r commit parent file fn < <(node -e 'const m = require(process.argv[1]); console.log(m.commit, m.parent, m.file, m.function)' "/home/user/strictts/scratch/hist_remeda/scan/$id/meta.json")
  row="$id\t$fn\t$file"
  for rev in "$parent" "$commit"; do
    src=$(git -C "$R" show "$rev:$file" 2>/dev/null || true)
    if [ -z "$src" ]; then e=no-file
    elif command grep -qE "^export (default )?(async )?function\*? ?$fn\b|^export (const|let|var) $fn\b|^export \{[^}]*\b$fn\b[^}]*\}|^export default $fn\b" <<< "$src"; then e=exported
    else e=internal; fi
    row="$row\t$e"
  done
  printf "$row\n" >> "$OUT"
done
awk -F'\t' 'NR>1 {c[$4" / "$5]++} END {for (k in c) print c[k], k}' "$OUT"
