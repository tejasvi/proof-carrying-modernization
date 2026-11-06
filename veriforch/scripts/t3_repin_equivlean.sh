#!/usr/bin/env bash
# T3 (PREREG_T_v1) certificate pins: equiv-lean EQUIVLEAN_SHA built against T3's cirlean, the steps of
# scripts/repin_equivlean.sh 1-3 (clone of ~/equivlean, its lakefile pointing at deps/cirlean-<cirlean sha>, the modules
# certificates import built under run1.sh), in a directory named after both commits, as PREREG_C1b's launch did
# (deps/equivlean-<sha7>-cir-<cirlean7>; repin_equivlean.sh's deps/equivlean-<sha7> could later be re-pointed at another
# cirlean by a second run). scripts/cert_pin.env is NOT switched: the result goes to the T3 pin file, with T3's Java and
# Rust pins, for scripts/prereg_t3.py --pins. Before the build, `lake build --no-build +CIR` must pass: the shared cirlean
# directory is up to date and nothing is rebuilt in it. Then the cidemo smoke pairs of repin_equivlean.sh (step 5) run
# with the new pins (vo ci --budget 0) and their verdict lines are printed with the expected ones.
#
#   scripts/t3_repin_equivlean.sh EQUIVLEAN_SHA CIRLEAN_SHA PIN_FILE [JIMPLE_SNAPSHOT [AENEAS_PIN EQUIVLEAN_AENEAS_PIN]]
set -eu
VO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
EQ="${1:?usage: t3_repin_equivlean.sh EQUIVLEAN_SHA CIRLEAN_SHA PIN_FILE [JIMPLE_SNAPSHOT [AENEAS_PIN EQ_AENEAS_PIN]]}"
CIR="${2:?cirlean sha}"
PIN="${3:?pin file}"
JS="${4:-20261025T0300Z}"
AEN="${5:-aeneas-fdebf20}"
EQA="${6:-equivlean-7e1aaf0}"
EQ7="${EQ:0:7}"; CIR7="${CIR:0:7}"
CIRDIR="$VO_ROOT/deps/cirlean-$CIR7"
EQDIR="$VO_ROOT/deps/equivlean-$EQ7-cir-$CIR7"
LOGDIR="$(dirname "$PIN")"
[ ! -e "$PIN" ] || { echo "pin file $PIN exists: not overwritten" >&2; exit 2; }
mkdir -p "$LOGDIR"
[ -x "$CIRDIR/.lake/build/bin/cir2lean" ] || { echo "no built cirlean at $CIRDIR" >&2; exit 2; }
case "$(git -C "$CIRDIR" rev-parse HEAD)" in "$CIR"*) ;; *) echo "$CIRDIR is not at $CIR" >&2; exit 2 ;; esac
[ -d "$VO_ROOT/deps/JimpleLean-$JS" ] || { echo "no deps/JimpleLean-$JS" >&2; exit 2; }
[ -d "$VO_ROOT/deps/$AEN" ] || { echo "no deps/$AEN" >&2; exit 2; }
[ -d "$VO_ROOT/deps/$EQA-aeneas" ] || { echo "no deps/$EQA-aeneas" >&2; exit 2; }
if [ ! -d "$EQDIR" ]; then
  git clone -q "$HOME/equivlean" "$EQDIR"
  git -C "$EQDIR" checkout -q "$EQ"
fi
case "$(git -C "$EQDIR" rev-parse HEAD)" in "$EQ"*) ;; *) echo "$EQDIR is not at $EQ" >&2; exit 2 ;; esac
cat > "$EQDIR/lakefile.toml" <<EOF
name = "equivlean"
version = "0.1.0"
defaultTargets = ["EquivLean"]

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

# veriforch's pinned copy of equiv-lean ($EQ) for PREREG_T_v1 T3, built against veriforch's pinned cirlean
# (deps/cirlean-$CIR7), so its oleans and the generated modules share one CIR. Only the modules certificates import
# (and their imports) are built here; every module of the package belongs to the library so that imports resolve.
[[require]]
name = "cirlean"
path = "../cirlean-$CIR7"

[[lean_lib]]
name = "EquivLean"
globs = ["EquivLean.+"]
EOF
rm -f "$EQDIR/lake-manifest.json"
B="$LOGDIR/build_equivlean_${EQ7}_${CIR7}.log"
"$VO_ROOT/scripts/run1.sh" -t 900 -m 32 -c 0.2 -- bash -c "cd '$EQDIR' && lake build --no-build +CIR" > "$B.nobuild" 2>&1 \
  || { echo "cirlean $CIRDIR is not up to date for this package (lake build --no-build +CIR failed: $B.nobuild): nothing built" >&2; exit 3; }
"$VO_ROOT/scripts/run1.sh" -t 3600 -m 128 -c 2 -- bash -c "cd '$EQDIR' && lake build EquivLean.Core.Facts \
  EquivLean.Bridge.Cir.Tactic EquivLean.Bridge.Cir.Obs EquivLean.Bridge.Cir.AutoCouple EquivLean.Bridge.Cir.PtrArgs" \
  > "$B" 2>&1 || { echo "equiv-lean build failed: $B" >&2; exit 1; }
echo "built $EQDIR against $CIRDIR (log $B)"
cat > "$PIN" <<EOF
# PREREG_T_v1 T3 pins for scripts/prereg_t3.py --pins (given to every \`vo ci\` as VO_CERT_PIN_ENV). Made by
# scripts/t3_repin_equivlean.sh $EQ $CIR on $(date -u +%Y-%m-%dT%H:%M:%SZ).
# C and C++: the compared builds and the certificates on cirlean $CIR7, equiv-lean $EQ7 built on that same cirlean.
VO_CIRLEAN_DIR="\$VO_ROOT/deps/cirlean-$CIR7"
VO_CIRLEAN_PIN=$CIR7
VO_CERT_CIRLEAN_DIR="\$VO_ROOT/deps/cirlean-$CIR7"
VO_CERT_CIRLEAN_PIN=$CIR7
VO_EQUIVLEAN_DIR="\$VO_ROOT/deps/equivlean-$EQ7-cir-$CIR7"
VO_EQUIVLEAN_PIN=equivlean-$EQ7-cir-$CIR7
# Java: T1's JimpleLean snapshot (the D2 pin).
VO_JIMPLE_DIR="\$VO_ROOT/deps/JimpleLean-$JS"
VO_JIMPLE_PIN=snapshot-$JS
# Rust: T1's Charon + Aeneas and equiv-lean's Aeneas bridge.
VO_AENEAS_DIR="\$VO_ROOT/deps/$AEN"
VO_AENEAS_PIN=$AEN
VO_EQUIVLEAN_AENEAS_DIR="\$VO_ROOT/deps/$EQA-aeneas"
VO_EQUIVLEAN_AENEAS_PIN=$EQA
EOF
echo "pin file $PIN sha256 $(sha256sum "$PIN" | cut -c1-64)"
SM="$LOGDIR/smoke_${EQ7}_${CIR7}"
mkdir -p "$SM"
for r in "scratch/core/cidemo.toml 1314c1f 5433813 abs_diff=equivalent,clamp_add=changed_only_where_old_unsafe,sign=behaviour_changed" \
         "scratch/core/cidemo.toml b88e74c 018ebeb get_or=equivalent,sum_arr=equivalent,swap=equivalent"; do
  set -- $r
  echo "== $1 $2..$3 expected: $4"
  VO_CERT_PIN_ENV="$PIN" VO_CI_RUN_DIR="$SM/$(basename "$1" .toml)_$2" "$VO_ROOT/scripts/vo" ci "$VO_ROOT/$1" \
    --base "$2" --head "$3" --attempts 0 --budget 0 --check-timeout 600 > "$SM/$(basename "$1" .toml)_$2.log" 2>&1 || true
  command grep -E "equivalence |blocked" "$SM/$(basename "$1" .toml)_$2.log" || echo "  (no verdict lines: see $SM)"
done
