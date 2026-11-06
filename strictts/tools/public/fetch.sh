#!/usr/bin/env bash
# Fetch the public projects measured in tools/public/RESULTS.md at pinned versions, each into its
# own new directory scratch/projects/<name> (gitignored; the sources are not committed). Nothing
# from the projects is run: shallow clone of one tag or commit, then a check of the commit hash.
#   tools/public/fetch.sh [name...]      (default: all)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEST="$ROOT/scratch/projects"
mkdir -p "$DEST"

# name  url  ref (tag, or - for a bare commit)  commit
PROJECTS=(
  "es-toolkit https://github.com/toss/es-toolkit v1.52.0 32f4c8fb33828ad6512064ba84b0fdd8fda966a3"
  "thealgorithms-ts https://github.com/TheAlgorithms/TypeScript - 19b4ced86c99815f142d4a46a028f55487b8038a"
)

want=("$@")
for p in "${PROJECTS[@]}"; do
  read -r name url ref sha <<< "$p"
  if [ ${#want[@]} -gt 0 ] && [[ ! " ${want[*]} " == *" $name "* ]]; then continue; fi
  d="$DEST/$name"
  if [ -e "$d" ]; then
    have=$(git -C "$d" rev-parse HEAD 2>/dev/null || echo none)
    if [ "$have" = "$sha" ]; then echo "$name: present at $sha"; continue; fi
    echo "$name: $d exists but is not at $sha (have $have); move it away first" >&2; exit 1
  fi
  if [ "$ref" != "-" ]; then
    git -c advice.detachedHead=false clone -q --depth 1 --branch "$ref" "$url" "$d"
  else
    git init -q "$d"
    git -C "$d" fetch -q --depth 1 "$url" "$sha"
    git -C "$d" -c advice.detachedHead=false checkout -q FETCH_HEAD
  fi
  have=$(git -C "$d" rev-parse HEAD)
  if [ "$have" != "$sha" ]; then echo "$name: fetched $have, expected $sha" >&2; exit 1; fi
  echo "$name: fetched $ref at $sha"
done
