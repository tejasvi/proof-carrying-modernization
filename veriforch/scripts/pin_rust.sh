#!/usr/bin/env bash
# Pin the Rust bridge of veriforch (adapters/rust): Charon + Aeneas fdebf20 (the binaries and Aeneas's Lean library,
# copied from equiv-lean's setup) and equiv-lean's Aeneas bridge (EquivLean.Bridge.Aeneas.*, for the CI old ≡ new
# verdicts), built against that library. mathlib and the other Lean packages are read in place from equiv-lean's
# workspace (~/equivlean/.lake/packages) at the revisions of Aeneas's lake-manifest.json (adapters/rust/build.py
# checks them on every build).
#
#   bash scripts/pin_rust.sh [EQUIVLEAN_SHA (default 7e1aaf0)]
#
# Steps (each skipped when done): 1. copy ~/equivlean_work/dl/rel/aeneas_bin -> deps/aeneas-fdebf20/bin and
# ~/equivlean_work/dl/aeneas/backends/lean (with its build) -> deps/aeneas-fdebf20/lean, and record sha256 of the
# binaries in deps/aeneas-fdebf20/SHA256; 2. clone equiv-lean into deps/equivlean-<sha>-aeneas at <sha>; 3. compile
# the 8 modules of the Aeneas bridge's import closure with `lean -o` in import order (no lake: Aeneas's lakefile would
# fetch mathlib) under run1.sh.
set -eu
VO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
EQ="${1:-7e1aaf0}"
EQ7="${EQ:0:7}"
AD="$VO_ROOT/deps/aeneas-fdebf20"
ED="$VO_ROOT/deps/equivlean-$EQ7-aeneas"
if [ ! -d "$AD" ]; then
  mkdir "$AD"
  cp -r "$HOME/equivlean_work/dl/rel/aeneas_bin" "$AD/bin"
  cp -r "$HOME/equivlean_work/dl/aeneas/backends/lean" "$AD/lean"
fi
[ -f "$AD/SHA256" ] || (cd "$AD/bin" && sha256sum aeneas charon charon-driver rust-toolchain > "$AD/SHA256")
(cd "$AD/bin" && sha256sum -c --quiet "$AD/SHA256")
if [ ! -d "$ED" ]; then
  git clone -q "$HOME/equivlean" "$ED"
  git -C "$ED" checkout -q "$EQ"
fi
case "$(git -C "$ED" rev-parse HEAD)" in "$EQ"*) ;; *) echo "$ED is not at $EQ" >&2; exit 2 ;; esac
# each `lean` compile runs under run1.sh (build.py: build_bridge)
VO_ROOT="$VO_ROOT" VO_EQUIVLEAN_AENEAS_DIR="$ED" python3 -I "$VO_ROOT/orch/veriforch/adapters/rust/pin_bridge.py" "$ED" \
  > "$VO_ROOT/runs/build_equivlean_${EQ7}_aeneas.log" 2>&1 \
  || { echo "bridge build failed: runs/build_equivlean_${EQ7}_aeneas.log" >&2; exit 1; }
echo "pinned: $AD, $ED"
