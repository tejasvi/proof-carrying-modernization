#!/bin/bash
# Pair-by-pair comparison of two per-pair tables (columns id ... cat ... reason ..., by header name):
# every pair whose verdict category differs, with both reasons, then the counts of each change.
#   bash scratch/compare_tables.sh OLD_TABLE NEW_TABLE OLD_LABEL NEW_LABEL > OUT.tsv
set -euo pipefail
awk -F'\t' -v lo="$3" -v ln="$4" '
  FNR == 1 { for (i = 1; i <= NF; i++) col[FILENAME, $i] = i; next }
  FILENAME == ARGV[1] { c = $col[FILENAME, "cat"]; r = $col[FILENAME, "reason"]; oc[$1] = c; orr[$1] = r; next }
  {
    id = $1; c = $col[FILENAME, "cat"]; r = $col[FILENAME, "reason"]; seen[id] = 1
    if (!(id in oc)) { print id "\t(missing in " lo ")\t" c "\t\t" r; n["missing in " lo]++; next }
    if (oc[id] != c) { print id "\t" oc[id] "\t" c "\t" substr(orr[id], 1, 160) "\t" substr(r, 1, 160); n[oc[id] " -> " c]++ }
  }
  END {
    for (id in oc) if (!(id in seen)) { print id "\t" oc[id] "\t(missing in " ln ")"; n["missing in " ln]++ }
    for (k in n) print "#\t" n[k] "\t" k
  }' "$1" "$2"
