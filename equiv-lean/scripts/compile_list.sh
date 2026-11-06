#!/bin/bash
# Compile the given modules (paths) in order with lean1.sh -o; stop at the first failure.
cd "$(dirname "$0")/.." || exit 2
for f in "$@"; do
  start=$(date +%s)
  if ! LRUN_AS=134217728 scripts/lean1.sh -o "$f" > .lake/last.log 2>&1 || grep -q "error" .lake/last.log; then
    echo "FAIL $f"; grep -E "error" -A6 .lake/last.log | head -40; exit 1
  fi
  echo "ok $f ($(( $(date +%s) - start )) s)"
done
