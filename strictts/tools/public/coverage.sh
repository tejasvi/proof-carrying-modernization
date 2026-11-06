#!/usr/bin/env bash
# Coverage (and --emit-lean) of one fetched public project in one translator mode. Run it under
# the guarded runner from the worktree root:
#   tools/run.sh 0.2 590 tools/public/coverage.sh MODE NAME
# MODE strict: the translator's --strict (the original subset: `unknown` and `any` rejected).
# MODE dyn:    the default: values of type `unknown` (and `any`) are the checked dynamic type.
# The project is only read; tools/public/tsconfig/NAME.json is copied next to its tsconfig.json
# (it extends the project's own compiler options and selects the source files: no tests).
# Outputs: PUB/out/NAME.MODE.json (report), PUB/lean/Cov_NAME_MODE.lean (PUB defaults to
# scratch/public). TREE (default: this tree) is the StrictTS tree whose translator is measured,
# e.g. a git-archive copy of a fixed commit. EMIT_FLAGS (default empty): more translator flags, e.g.
# --no-emit-generics (from 881c69c on the module holds the covered generic functions at one instance
# by default; the uniform NoPanic sweep attempts them through the T := number wrappers instead).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TREE=${TREE:-$ROOT}; PUB=${PUB:-$ROOT/scratch/public}
MODE=${1:?mode strict|dyn}; NAME=${2:?project name}
case "$MODE" in
  strict) FLAGS=(--strict) ;;
  dyn) FLAGS=() ;;
  *) echo "unknown mode $MODE" >&2; exit 2 ;;
esac
P="$ROOT/scratch/projects/$NAME"
[ -f "$P/tsconfig.json" ] || { echo "missing $P (run tools/public/fetch.sh)" >&2; exit 2; }
CFG="$P/tsconfig.strictts.json"
cmp -s "$ROOT/tools/public/tsconfig/$NAME.json" "$CFG" || { cp "$ROOT/tools/public/tsconfig/$NAME.json" "$CFG.$$"; mv "$CFG.$$" "$CFG"; }
OUT="$PUB/out"; LEAN="$PUB/lean"
mkdir -p "$OUT" "$LEAN"
LABEL="${NAME}_${MODE}"
node "$TREE/frontend/dist/cli.js" --coverage "${FLAGS[@]}" -p "$CFG" --report "$OUT/$NAME.$MODE.json" --label "$LABEL" \
  --emit-lean "$LEAN/Cov_$(echo "$LABEL" | tr -c 'A-Za-z0-9_\n' '_').lean" ${EMIT_FLAGS:-}
