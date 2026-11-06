#!/usr/bin/env bash
# usage: orch_chk.sh FILE.lean  -- elaborate a check file with scratch/f64eval/$ORCH (default orch) on LEAN_PATH
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
LP=$(lake env printenv LEAN_PATH)
exec env LEAN_PATH="$LP:$ROOT/scratch/f64eval/${ORCH:-orch}" lean "$@"
