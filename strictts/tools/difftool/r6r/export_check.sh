#!/bin/bash
# R6r: is the function of each refuted pair exported by its module, in the original source of both
# versions (git show from the no-checkout remeda clone; the run's slices add an export for the target,
# so they cannot answer this)? Writes scratch/r7/refuted_export.tsv (pair, function, file, old, new).
#   bash scratch/r7/export_check.sh
set -euo pipefail
cd /home/user/strictts
R=scratch/projects_hist/remeda
OUT=scratch/r7/refuted_export.tsv
printf 'pair\tfunction\tfile\told\tnew\n' > "$OUT"
awk -F'\t' 'NR>1 {print $1}' scratch/r7/tscheck.tsv | sort --parallel=1 -u |
while read -r id; do
  read -r commit parent file fn < <(node -e 'const m = require(process.argv[1]); console.log(m.commit, m.parent, m.file, m.function)' "$PWD/scratch/hist_remeda/scan/$id/meta.json")
  row="$id\t$fn\t$file"
  for rev in "$parent" "$commit"; do
    src=$(git -C "$R" show "$rev:$file" 2>/dev/null || true)
    if [ -z "$src" ]; then e=no-file
    elif printf '%s\n' "$src" | command grep -qE "^export (default )?(async )?function\*? ?$fn\b|^export (const|let|var) $fn\b|^export \{[^}]*\b$fn\b[^}]*\}|^export default $fn\b"; then e=exported
    else e=internal; fi
    row="$row\t$e"
  done
  printf "$row\n" >> "$OUT"
done
awk -F'\t' 'NR>1 {c[$4" / "$5]++} END {for (k in c) print c[k], k}' "$OUT"
