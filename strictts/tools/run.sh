#!/usr/bin/env bash
# Guarded runner for every build/test command of this project.
#   usage: tools/run.sh CAP_COREH TIMEOUT_S cmd [args...]
# - meters CPU with coreh_guard_v2 (--run mode, exact) and stops the job at the cap
# - one core (taskset), nice 10, 64 GiB address-space cap (Lean needs > 32 GiB of reservations), scratch TMPDIR inside the project
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CAP=${1:?cap core-h}; TO=${2:?timeout s}; shift 2
mkdir -p "$ROOT/logs" "$ROOT/scratch/tmp"
export TMPDIR="$ROOT/scratch/tmp"
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1 MALLOC_ARENA_MAX=2
export PATH="$HOME/.elan/bin:$PATH"
CORE=${CORE:-$(( 300 + RANDOM % 80 ))}
AS=${AS_BYTES:-68719476736}
LOG="$ROOT/logs/guard_$(date -u +%Y%m%dT%H%M%SZ)_$$.log"
exec /usr/bin/python3 -I -B /home/user/cc50/rung3/shared_tools/coreh_guard_v2_20261023T0655Z/coreh_guard_v2.py \
  "$LOG" "$CAP" --margin 2 --run -- nice -n 10 taskset -c "$CORE" prlimit --as="$AS" -- timeout "$TO" "$@"
