#!/bin/bash
# Rebuild and re-check everything: library, proved examples (with their axioms), tests,
# reference interpreter, and the differential validations against GnuCOBOL / JDK / rustc.
# usage: scripts/check_all.sh [N]   (N random cases per validation, default 20)
set -u
cd "$(dirname "$0")/.."
N="${1:-20}"
echo "== library, examples, interpreter"
scripts/lrun.sh lake build Cobol Examples cobolrun 2>&1 | grep -E "error|axioms|Build completed" || true
echo "== tests"
for f in tests/*.lean; do
  if scripts/lean1.sh "$f" 2>&1 | grep -q "error"; then echo "FAIL $f"; else echo "ok   $f"; fi
done
echo "== semantics vs GnuCOBOL"
nice -n 10 python3 tools/difftest/difftest.py --n "$N" | sed -n 1p
nice -n 10 python3 tools/difftest/difftest.py --n "$N" --trunc bin | sed -n 1p
nice -n 10 python3 tools/difftest/ctrltest.py --n "$N" | sed -n 1p
echo "== extracted IR vs COBOL source (GnuCOBOL)"
for d in acctint binary recsum; do
  (cd "examples/$d" && nice -n 10 python3 validate.py --n "$N" | tail -1)
done
echo "== Lean transcriptions vs Java / Rust"
(cd tools/targettest && nice -n 10 python3 targettest.py --n "$N" | tail -1)
