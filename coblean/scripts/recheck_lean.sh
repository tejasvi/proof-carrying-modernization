#!/bin/bash
# Elaborate Lean files against the snapshot's built library and print their messages (the
# `#print axioms` lines). Writes nothing outside $OUT. 1 Lean thread, no async elaboration.
# usage: C=<snapshot root> OUT=<scratch dir> $C/scripts/recheck_lean.sh Examples/X.lean ...
set -u
: "${C:?set C to the snapshot root}" "${OUT:?set OUT to a scratch directory}"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0
mkdir -p "$OUT/tmp"
export LEAN_PATH="$C/.lake/build/lib/lean:$TC/lib/lean" LEAN_NUM_THREADS=1 TMPDIR="$OUT/tmp"
cd "$C" || exit 2
rc=0
for f in "$@"; do "$TC/bin/lean" -DElab.async=false "$f" || rc=1; done
exit $rc
