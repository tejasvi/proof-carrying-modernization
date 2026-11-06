#!/usr/bin/env bash
# Coverage of one project (read-only on the project; outputs in tests/coverage/).
#   tests/coverage/run_project.sh LABEL TSCONFIG [--only-dir DIR]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LABEL=$1; CFG=$2; shift 2
OUT="$ROOT/tests/coverage/$(echo "$LABEL" | tr '/' '-').json"
exec node "$ROOT/frontend/dist/cli.js" --coverage -p "$CFG" --report "$OUT" --label "$LABEL" "$@"
