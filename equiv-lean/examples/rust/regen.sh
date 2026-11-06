#!/bin/bash
# Regenerate the Aeneas Lean code of one example crate:  examples/rust/regen.sh <crate-dir> <LeanName>
#   charon (preset aeneas) -> <crate>.llbc -> aeneas -backend lean -split-files
#   -> EquivLean/Demo/Gen/Aeneas/<LeanName>/{Types,Funs}.lean (+ FunsExternal_Template.lean kept
#   next to the crate when the crate calls external functions; FunsExternal.lean is hand-written).
#   Extra aeneas flags in AENEAS_FLAGS, e.g. AENEAS_FLAGS="-max-recdepth 100000" for crc32fast_base
#   (its 16 x 256 table constant exceeds the default recursion depth 2048 of the generated file).
#   The output goes into the worktree that contains the crate (not always master's), and each run
#   writes a fresh, timestamped scratch directory instead of deleting the previous one.
set -e
B=/home/user/equivlean_work/dl/rel/aeneas_bin
S=/home/user/equivlean_work/scratch/eq-aeneas
C="$(realpath "$1")"; N="$2"
R="$(git -C "$C" rev-parse --show-toplevel)"
[ -f "$R/lakefile.toml" ] || { echo "regen.sh: $C is not inside an equiv-lean worktree" >&2; exit 2; }
# the crate's name (Charon names the .llbc after it), else the directory name
name="$(sed -n 's/^name *= *"\([A-Za-z0-9_-]*\)".*/\1/p' "$C/Cargo.toml" | head -1)"
name="${name:-$(basename "$C")}"
export TMPDIR=$S/tmp CARGO_TARGET_DIR=$S/target; mkdir -p "$TMPDIR" "$CARGO_TARGET_DIR"
ulimit -v 33554432
(cd "$C" && nice -n 10 "$B/charon" cargo --preset=aeneas -- -j1)
out=$S/gen/$name-$(date -u +%Y%m%dT%H%M%SZ)-$$; mkdir -p "$out"
nice -n 10 "$B/aeneas" -backend lean -split-files -no-progress-bar ${AENEAS_FLAGS:-} \
  -subdir "EquivLean/Demo/Gen/Aeneas/$N" -dest "$out" "$C/$name.llbc"
G=$R/EquivLean/Demo/Gen/Aeneas/$N; mkdir -p "$G"
cp "$out/EquivLean/Demo/Gen/Aeneas/$N/Types.lean" "$out/EquivLean/Demo/Gen/Aeneas/$N/Funs.lean" "$G/"
if [ -f "$out/EquivLean/Demo/Gen/Aeneas/$N/FunsExternal_Template.lean" ]; then
  cp "$out/EquivLean/Demo/Gen/Aeneas/$N/FunsExternal_Template.lean" "$C/"
fi
