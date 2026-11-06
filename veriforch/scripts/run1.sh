#!/usr/bin/env bash
# Run one job under the main-VM rules: 1 thread, address-space cap, nice 10,
# wall-clock timeout, project-local TMPDIR, and the core-hour guard (--run mode).
#
#   scripts/run1.sh [-t SECONDS] [-m GIB] [-c CORE_H] [-l LOG] -- CMD ARGS...
#
# Defaults: -t 600, -m 32, -c 0.25, -l $VO_ROOT/runs/guard.log
# VO_GUARD_LOG, when set, is the guard log of every job of the run, whatever -l says (one log per run, so a run's
# core-seconds can be read from its own log; e.g. one per pre-registered CI step).
set -u
VO_ROOT="${VO_ROOT:-/home/user/veriforch}"
T=600; M=32; C=0.25; L="$VO_ROOT/runs/guard.log"
while [ $# -gt 0 ]; do
  case "$1" in
    -t) T="$2"; shift 2 ;;
    -m) M="$2"; shift 2 ;;
    -c) C="$2"; shift 2 ;;
    -l) L="$2"; shift 2 ;;
    --) shift; break ;;
    *) break ;;
  esac
done
[ $# -gt 0 ] || { echo "usage: run1.sh [-t S] [-m GIB] [-c COREH] [-l LOG] -- CMD..." >&2; exit 2; }
[ -n "${VO_GUARD_LOG:-}" ] && L="$VO_GUARD_LOG"
GUARD=/home/user/cc50/rung3/shared_tools/coreh_guard_v2_20261023T0655Z/coreh_guard_v2.py
export TMPDIR="$VO_ROOT/scratch/tmp"
mkdir -p "$TMPDIR" "$(dirname "$L")"
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1 MALLOC_ARENA_MAX=2
ulimit -v $((M * 1024 * 1024))
# The timeout runs INSIDE the guard: the guard is the subreaper of the whole tree, `timeout` kills the job's
# process group at T and SIGKILLs it 30 s later, and the outer timeout is only a backstop for the guard.
if [ -f "$GUARD" ]; then
  # --poll 1: the guard notices the job's exit within a second (its 5 s default quantised every wall time)
  exec nice -n 10 timeout -k 30 $((T + 120)) python3 -I -B "$GUARD" "$L" "$C" --margin 5 --poll 1 --run -- \
    timeout -k 30 "$T" "$@"
else
  exec nice -n 10 timeout -k 30 "$T" "$@"
fi
