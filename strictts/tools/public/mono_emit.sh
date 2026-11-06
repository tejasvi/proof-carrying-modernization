#!/usr/bin/env bash
# Generic functions at one instance: monomorphic wrappers (tools/public/mono.js) for the covered
# generic functions of NAME's coverage report in MODE, then a coverage run with --emit-lean on
# the wrappers (the module holds the wrappers and the instances they call). With KIND cb, the
# wrappers instead pass one fixed pure function for every callback parameter (mono.js
# --callbacks). Run it under the guarded runner from the worktree root, after
# tools/public/coverage.sh MODE NAME:
#   tools/run.sh 0.2 590 tools/public/mono_emit.sh MODE NAME [mono|cb]
# Outputs: scratch/public/mono/NAME-MODE or NAME-cb-MODE (wrappers),
# scratch/public/out/NAME-KIND.MODE.json, scratch/public/lean/Cov_NAME_KIND_MODE.lean.
# TREE and PUB as in coverage.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TREE=${TREE:-$ROOT}; PUB=${PUB:-$ROOT/scratch/public}
MODE=${1:?mode strict|dyn}; NAME=${2:?project name}
case "$MODE" in
  strict) FLAGS=(--strict) ;;
  dyn) FLAGS=() ;;
  *) echo "unknown mode $MODE" >&2; exit 2 ;;
esac
KIND=${3:-mono}
case "$KIND" in
  mono) W="$PUB/mono/$NAME-$MODE"; MFLAGS=() ;;
  cb) W="$PUB/mono/$NAME-cb-$MODE"; MFLAGS=(--callbacks) ;;
  *) echo "unknown kind $KIND" >&2; exit 2 ;;
esac
mkdir -p "$W"
node "$ROOT/tools/public/mono.js" "$ROOT/scratch/projects/$NAME" "$PUB/out/$NAME.$MODE.json" "$W" "${MFLAGS[@]}"
LABEL="${NAME}_${KIND}_${MODE}"
node "$TREE/frontend/dist/cli.js" --coverage "${FLAGS[@]}" -p "$W/tsconfig.json" --report "$PUB/out/$NAME-$KIND.$MODE.json" \
  --label "$LABEL" --emit-lean "$PUB/lean/Cov_$(echo "$LABEL" | tr -c 'A-Za-z0-9_\n' '_').lean"
