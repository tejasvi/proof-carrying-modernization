#!/bin/bash
# Regenerate the StrictTS Lean code of the TypeScript examples with the pinned front end.
#   examples/ts/regen.sh            all examples
#   examples/ts/regen.sh pr_old     one example (examples/ts/pr_old.ts -> Gen/TS/PrOld.lean)
# The pinned copy (../equivlean_work/vendor/strictts-a15926a @a15926a) is only read: its
# frontend/{dist,lib} is copied to a scratch directory named after the pin, together with
# typescript 5.9.3 (the version its package-lock.json pins; the pinned copy ships no
# node_modules), and run from there.  A new pin needs a new scratch directory (the copy is made
# only once).
# Output: EquivLean/Demo/Gen/TS/<CamelName>.lean, namespace EquivLean.Demo.Gen.TS.<CamelName>,
# in the repository (or worktree) that contains this script.
set -e
R="$(cd "$(dirname "$0")/../.." && pwd)"
V=/home/user/equivlean_work/vendor/strictts-a15926a
S=/home/user/equivlean_work/scratch/eq-ts2/frontend-a15926a
export TMPDIR=$S/tmp; mkdir -p "$TMPDIR"
ulimit -v 67108864
if [ ! -f "$S/frontend/dist/cli.js" ]; then
  mkdir -p "$S/frontend/node_modules"
  cp -r "$V/frontend/dist" "$V/frontend/lib" "$V/frontend/package.json" "$S/frontend/"
  cp -r /home/user/strictts/frontend/node_modules/typescript "$S/frontend/node_modules/"
fi
cd "$R"
names="${1:-pr_old pr_new fnv_bytes scale_old scale_new pos_old pos_new digits_old digits_new pako_crc32 poly_hash fnv_while}"
for n in $names; do
  camel="$(echo "$n" | sed -E 's/(^|_)([a-z])/\U\2/g')"
  nice -n 10 node "$S/frontend/dist/cli.js" --namespace "EquivLean.Demo.Gen.TS.$camel" \
    -o "EquivLean/Demo/Gen/TS/$camel.lean" "examples/ts/$n.ts"
done
