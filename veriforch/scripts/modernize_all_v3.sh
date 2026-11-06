#!/usr/bin/env bash
# Item A (v3: --seed for repetitions; seed 1 is the run of record): translation + counterexample repair runs for
# the given programs, both arms, both languages, at most $JOBS at a time, each under run1.sh. Logs:
# runs/modernize/<PROG>/<arm>/<lang>[_s<seed>]/log.txt and runs/modernize/_logs/.
#
#   scripts/modernize_all_v3.sh [--jobs N] [--budget D] [--seed S] [--arms "guided naive"] [--langs "java rust"] PROG...
set -u
VO_ROOT=/home/user/veriforch
JOBS=4; BUDGET=15; ARMS="guided naive"; LANGS="java rust"; SEED=1
while [ $# -gt 0 ]; do
  case "$1" in
    --jobs) JOBS="$2"; shift 2 ;;
    --budget) BUDGET="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --arms) ARMS="$2"; shift 2 ;;
    --langs) LANGS="$2"; shift 2 ;;
    *) break ;;
  esac
done
SUF=""; [ "$SEED" = 1 ] || SUF="_s$SEED"
mkdir -p "$VO_ROOT/runs/modernize/_logs"
export PYTHONPATH="$VO_ROOT/orch" OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
for prog in "$@"; do
  for arm in $ARMS; do
    for lang in $LANGS; do
      while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 5; done
      log="$VO_ROOT/runs/modernize/_logs/${prog}_${arm}_${lang}${SUF}.log"
      echo "$(date -u +%H:%M:%SZ) start $prog $arm $lang seed $SEED"
      "$VO_ROOT/scripts/run1.sh" -t 14400 -m 96 -c 6 -- "$VO_ROOT/.venv/bin/python" -B -m veriforch.modernize.loop \
        "$prog" "$arm" "$lang" --budget "$BUDGET" --seed "$SEED" > "$log" 2>&1 &
    done
  done
done
wait
echo "$(date -u +%H:%M:%SZ) all done"
