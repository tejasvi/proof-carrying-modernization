#!/bin/bash
# Light-work wrapper for the shared main VM: 1 Lean thread, address-space cap (default 32 GB,
# LRUN_AS in KB), nice 10, timeout (default 10 min, LRUN_TIMEOUT).
ulimit -v ${LRUN_AS:-33554432}
export LEAN_NUM_THREADS=1
cd "$(dirname "$0")/.." || exit 2
# bv_decide writes its LRAT proof to a temporary file: keep those inside the project
mkdir -p .lake/tmp; export TMPDIR="$PWD/.lake/tmp"
exec nice -n 10 timeout "${LRUN_TIMEOUT:-600}" "$@"
