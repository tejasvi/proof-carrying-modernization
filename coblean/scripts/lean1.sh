#!/bin/bash
# Elaborate one file against the built library: 1 Lean thread, no async elaboration,
# 32 GB address-space cap, nice 10, timeout (default 10 min).
ulimit -v ${LRUN_AS:-33554432}
D="$(cd "$(dirname "$0")/.." && pwd)"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0
export LEAN_PATH="$D/.lake/build/lib/lean:$TC/lib/lean"
export LEAN_NUM_THREADS=1
# bv_decide writes its LRAT proof to a temporary file: keep those inside the project
mkdir -p "$D/.lake/tmp"; export TMPDIR="$D/.lake/tmp"
exec nice -n 10 timeout "${LRUN_TIMEOUT:-600}" "$TC/bin/lean" -DElab.async=false "$@"
