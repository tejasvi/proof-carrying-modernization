#!/usr/bin/env bash
# Run one proof-attempt file written by tools/public/attempts.py (one guarded job, under 10
# minutes); the emitted modules' .olean files (tools/public/elab.sh) are found next to them:
#   tools/public/prove.sh scratch/public/auto/Cov_X_auto_K.lean
# output: the same path with .out (Lean messages), and one summary line on stdout.
# TREE (default: this tree): the StrictTS tree whose library and tactics run the file; the
# modules are found in the file's own directory's ../lean and in ../diag (PUB layout), or in
# scratch/public/lean; TIMEOUT (default 590 s) and CAP (core-h, default 0.2) bound the job.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TREE=${TREE:-$ROOT}
f=$(realpath "$1"); out="${f%.lean}.out"
export PATH="$HOME/.elan/bin:$PATH"
LP=$(cd "$TREE" && lake env printenv LEAN_PATH)
D=$(dirname "$f")/..
export LEAN_PATH="$LP:$D/lean:$D/diag:$ROOT/scratch/public/lean"
t0=$(date +%s.%N)
( cd "$TREE" && "$ROOT/tools/run.sh" "${CAP:-0.2}" "${TIMEOUT:-590}" lean -DElab.async=false "$f" ) > "$out" 2>&1
rc=$?
t1=$(date +%s.%N)
printf '%s rc=%s secs=%.1f axioms_lines=%s errors=%s\n' "$(basename "$f")" "$rc" "$(echo "$t1 - $t0" | bc)" "$(grep -c 'depends on axioms' "$out")" "$(grep -c ': error' "$out")"
