#!/bin/bash
# Light-work wrapper for the shared main VM: 1 Lean thread, address-space cap (default 64 GiB,
# LRUN_AS in KiB), nice 10, timeout (default 10 min, LRUN_TIMEOUT).
ulimit -v ${LRUN_AS:-67108864}
export LEAN_NUM_THREADS=1
cd "$(dirname "$0")/.." || exit 2
# bv_decide writes its LRAT proof to a temporary file: keep those inside the project
mkdir -p .lake/tmp; export TMPDIR="$PWD/.lake/tmp"
exec nice -n 10 timeout "${LRUN_TIMEOUT:-600}" "$@"
