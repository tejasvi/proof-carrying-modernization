#!/usr/bin/env bash
# All shards of `validate.js run`, three at a time (each one guarded job under ten minutes),
# repeated until no function is left. Run from anywhere; extra arguments go to `run`:
#   tools/validate/run_all.sh                                  # the main pass
#   VALIDATE_WORK=scratch/validate_panics tools/validate/run_all.sh --panicked --single --record
# Shards per round: 3, or the number (1-3) in $VALIDATE_WORK/shards, read at the start of each
# round (to free job slots for other work while a long run goes on).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="${VALIDATE_WORK:-scratch/validate}"
case "$WORK" in /*) ;; *) WORK="$ROOT/$WORK" ;; esac
export VALIDATE_WORK="$WORK"
LOGS="$WORK/logs"
mkdir -p "$LOGS"
for round in $(seq 1 "${ROUNDS:-12}"); do
  ts=$(date -u +%Y%m%dT%H%M%SZ)
  n=3; [ -f "$WORK/shards" ] && n=$(tr -dc '0-9' < "$WORK/shards"); case "$n" in 1|2|3) ;; *) n=3 ;; esac
  for i in $(seq 0 $((n - 1))); do
    ( cd "$ROOT" && tools/run.sh 0.3 590 node tools/validate/validate.js run --shard "$i/$n" --budget "${BUDGET:-360}" "$@" \
        > "$LOGS/run_${ts}_s$i.log" 2>&1 ) &
  done
  wait
  left=$(cat "$LOGS"/run_"${ts}"_s*.log | awk '/functions to validate/ {s += $3} END {print s + 0}')
  done_n=$(cat "$LOGS"/run_"${ts}"_s*.log | awk '/functions recorded/ {s += $3} END {print s + 0}')
  echo "$(date -u +%H:%M:%SZ) round $round: $left functions pending, $done_n recorded"
  [ "$left" -le "$done_n" ] && break
done
