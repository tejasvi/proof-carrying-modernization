#!/usr/bin/env bash
# All ten projects (read-only on the projects), then the tables. Each project is one guarded
# job (tools/run.sh), well under 10 minutes.   tests/coverage/run_all.sh [SUFFIX]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SFX=${1:-}
# CM_ROOT / NP_ROOT: snapshots (git archive + node_modules links) for before/after measurements
C=${CM_ROOT:-/home/user/another-project-app}; N=${NP_ROOT:-/home/user/Downloads/second-project}
# COVERAGE_FLAGS: extra translator flags, e.g. --strict (the original subset, no unknown/any)
# CLI: another build of the translator (e.g. a git-archive copy, for before/after measurements)
CLI=${CLI:-$ROOT/frontend/dist/cli.js}
run() { "$ROOT/tools/run.sh" 0.3 590 node "$CLI" --coverage -p "$2" --report "$ROOT/tests/coverage/$(echo "$1" | tr '/' '-')$SFX.json" --label "$1" ${COVERAGE_FLAGS:-} "${@:3}" | head -1; }
for p in core chat import reach voice learn; do run another-project/functions/$p $C/functions/$p/tsconfig.json; done
run another-project/web $C/web/tsconfig.json
run another-project/telegram $C/telegram/tsconfig.json
run second-project/src $N/tsconfig.json --only-dir src
run second-project/functions $N/functions/tsconfig.json
