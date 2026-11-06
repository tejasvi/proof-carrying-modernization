#!/usr/bin/env bash
# A frozen copy of veriforch for a pre-registered run (pre-registrations C and D, R10: veriforch is not under git).
# The code (orch/, scripts/, VerifOrch/, tools/, targets/*.toml and targets/*.json) is copied and made read-only,
# with a SHA256 manifest (DEST/SHA256SUMS) of every copied file. deps/, runs/, scratch/ and .venv/ are symlinks to
# the live tree: the pins in deps/ are immutable directories, and outputs stay in the live runs/. Run the frozen code
# with DEST/scripts/vo, which sets VO_ROOT to DEST. A crash fix is a new copy plus `diff -ru OLD NEW` kept with the
# run's records.
#
#   scripts/freeze_copy.sh DEST        (DEST must not exist)
set -eu
SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEST="${1:?usage: freeze_copy.sh DEST}"
[ ! -e "$DEST" ] || { echo "freeze_copy: $DEST exists" >&2; exit 2; }
mkdir -p "$DEST/targets"
DEST="$(cd "$DEST" && pwd)"
for d in orch scripts VerifOrch tools; do
  rsync -a --exclude '__pycache__' --exclude '*.pyc' --exclude '*.new' "$SRC/$d/" "$DEST/$d/"
done
find "$SRC/targets" -maxdepth 1 -type f \( -name '*.toml' -o -name '*.json' \) -exec cp -p {} "$DEST/targets/" \;
for l in deps runs scratch .venv; do ln -s "$SRC/$l" "$DEST/$l"; done
(cd "$DEST" && find orch scripts VerifOrch tools targets -type f -print0 | sort -z | xargs -0 sha256sum) > "$DEST/SHA256SUMS"
chmod -R a-w "$DEST/orch" "$DEST/scripts" "$DEST/VerifOrch" "$DEST/tools" "$DEST/targets" "$DEST/SHA256SUMS"
echo "frozen copy $DEST: $(wc -l < "$DEST/SHA256SUMS") files, manifest sha256 $(sha256sum "$DEST/SHA256SUMS" | cut -c1-64)"
