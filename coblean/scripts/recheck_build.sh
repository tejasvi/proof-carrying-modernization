#!/bin/bash
# Rebuild the library, every proof and cobolrun from source, in a copy under $OUT (nothing is
# written in $C), and print the axiom lines and the build result. 1 Lean thread; about 30 min.
# usage: C=<snapshot root> OUT=<scratch dir> $C/scripts/recheck_build.sh
set -u
: "${C:?set C to the snapshot root}" "${OUT:?set OUT to a scratch directory}"
mkdir -p "$OUT/tree" "$OUT/tmp" || exit 2
tar -C "$C" --exclude=./.lake --exclude=./third_party --exclude='./tools/difftest/out*' \
  --exclude=./tools/targettest/out --exclude='./examples/*/out' -cf - . | tar -C "$OUT/tree" -xf - || exit 2
cd "$OUT/tree" || exit 2
export LEAN_NUM_THREADS=1 TMPDIR="$OUT/tmp"
"$HOME/.elan/bin/lake" build Cobol Examples cobolrun > "$OUT/build.log" 2>&1
rc=$?
grep -E "depends on axioms|error:|Build completed" "$OUT/build.log" | sed 's/^info: //'
exit $rc
