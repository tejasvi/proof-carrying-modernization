#!/bin/bash
# R6r: for every provable pair whose target is missing from the translation ("target X not found in the
# translation"), how the target is declared in the old version's slice: a module-level const/let/var
# bound to an arrow or function expression, a function declaration, or other.
# Writes scratch/r7/target_kind.tsv (pair, function, file, kind).
#   bash scratch/r7/target_kind.sh
set -euo pipefail
cd /home/user/strictts
T=scratch/r7/r6r_table.tsv
OUT=scratch/r7/target_kind.tsv
printf 'pair\tfunction\tfile\tkind\n' > "$OUT"
awk -F'\t' 'NR>1 && $8=="yes" && $11 ~ /^target .* not found in the translation/ {print $1"\t"$6"\t"$7}' "$T" |
while IFS=$'\t' read -r id fn file; do
  f=scratch/hist_remeda/scan/$id/old/$file
  if [ ! -e "$f" ]; then k=no-old-file
  else
    # the declaration line and the 7 lines after it (parameters may span lines)
    d=$(awk -v re="^(export )?(const|let|var) $fn( |:|=)" '$0 ~ re {n=8} n>0 {print; n--}' "$f")
    if [ -n "$d" ] && printf '%s\n' "$d" | command grep -qE '=>|function ?[(<]'; then k=module-const-function
    elif [ -n "$d" ]; then k=module-binding-other
    elif command grep -qE "^(export )?(async )?function\*? ?$fn\b" "$f"; then k=function-declaration
    else k=other; fi
  fi
  printf '%s\t%s\t%s\t%s\n' "$id" "$fn" "$file" "$k" >> "$OUT"
done
awk -F'\t' 'NR>1 {c[$4]++} END {for (k in c) print c[k], k}' "$OUT"
