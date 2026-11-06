#!/usr/bin/env bash
# Lean elaboration of one emitted module (one guarded job, under 10 minutes); run from anywhere:
#   tools/public/elab.sh scratch/public/lean/Cov_X.lean
# prints: module, lines, exit code, wall seconds, number of errors (log next to the file: .elab.log);
# also writes the module's .olean/.ilean next to it
# TREE (default: this tree): the StrictTS tree whose library elaborates the module.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TREE=${TREE:-$ROOT}
f=$(realpath "$1"); log="${f%.lean}.elab.log"
t0=$(date +%s.%N)
# the .olean (module name = file name) lets the proof-attempt files import the module
( cd "$TREE" && "$ROOT/tools/run.sh" 0.2 590 lake env lean -DElab.async=false -R "$(dirname "$f")" -o "${f%.lean}.olean" -i "${f%.lean}.ilean" "$f" ) > "$log" 2>&1
rc=$?
t1=$(date +%s.%N)
printf '%s lines=%s rc=%s secs=%.1f errors=%s\n' "$(basename "$f")" "$(wc -l < "$f")" "$rc" "$(echo "$t1 - $t0" | bc)" "$(grep -c ': error' "$log")"
