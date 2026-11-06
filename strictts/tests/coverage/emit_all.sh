#!/usr/bin/env bash
# Coverage of all ten projects with --emit-lean (one partial-program module per project in
# tests/coverage/lean/), then Lean elaboration of each module with its time. Read-only on the
# projects; every step is one guarded job (tools/run.sh), under 10 minutes.
#   tests/coverage/emit_all.sh [SUFFIX]      (reports <label>SUFFIX.json, default .emit)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SFX=${1:-.emit}
C=/home/user/another-project-app; N=/home/user/Downloads/second-project
L="$ROOT/tests/coverage/lean"; mkdir -p "$L"
run() {
  local f; f=$(echo "$1" | tr '/' '-')
  "$ROOT/tools/run.sh" 0.3 590 node "$ROOT/frontend/dist/cli.js" --coverage -p "$2" --report "$ROOT/tests/coverage/$f$SFX.json" \
    --label "$1" --emit-lean "$L/$f.lean" "${@:3}" | grep '^== emit-lean'
}
for p in core chat import reach voice learn; do run another-project/functions/$p $C/functions/$p/tsconfig.json; done
run another-project/web $C/web/tsconfig.json
run another-project/telegram $C/telegram/tsconfig.json
run second-project/src $N/tsconfig.json --only-dir src
run second-project/functions $N/functions/tsconfig.json
