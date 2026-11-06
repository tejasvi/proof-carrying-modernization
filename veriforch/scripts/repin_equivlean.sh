#!/usr/bin/env bash
# Re-pin the certificate side of `vo ci` / `vo patch` to an equiv-lean commit built against a cirlean that has
# `--link` (pre-registration C needs >= 88e6008). Steps:
#   1. clone equiv-lean (read-only source: ~/equivlean, whose worktrees share its branches) into deps/equivlean-<sha>,
#      check out <sha>;
#   2. write its lakefile in the pattern of deps/equivlean-32d231d: only the core and the cirlean bridge, with the
#      cirlean requirement pointing at deps/cirlean-<cirlean sha> (which must be that commit, already built);
#   3. build the modules certificates import (lake, under run1.sh);
#   4. unless --no-switch: replace scripts/cert_pin.env atomically with the new four pins (scheduler cirlean =
#      certificate cirlean, equiv-lean dir and pin);
#   5. unless --no-switch: smoke tests with the new pins, printed with the expected verdicts: cidemo
#      1314c1f..5433813 and b88e74c..018ebeb (classic path), tiny_regex_c_lib ef5deae..74ceb76 (modular build, a pair
#      outside the pre-registered sets).
#
#   scripts/repin_equivlean.sh [--no-switch] EQUIVLEAN_SHA [CIRLEAN_SHA (default 88e6008)]
set -eu
VO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SWITCH=1
[ "${1:-}" = "--no-switch" ] && { SWITCH=0; shift; }
EQ="${1:?usage: repin_equivlean.sh [--no-switch] EQUIVLEAN_SHA [CIRLEAN_SHA]}"
CIR="${2:-88e6008}"
EQ7="${EQ:0:7}"
CIRDIR="$VO_ROOT/deps/cirlean-$CIR"
EQDIR="$VO_ROOT/deps/equivlean-$EQ7"
[ -x "$CIRDIR/.lake/build/bin/cir2lean" ] || { echo "no built cirlean at $CIRDIR" >&2; exit 2; }
case "$(git -C "$CIRDIR" rev-parse HEAD)" in "$CIR"*) ;; *) echo "$CIRDIR is not at $CIR" >&2; exit 2 ;; esac
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

# veriforch's pinned copy of equiv-lean ($EQ), built against veriforch's pinned cirlean (deps/cirlean-$CIR), so its
# oleans and the generated modules share one CIR. Only the modules certificates import (and their imports) are
# built here; every module of the package belongs to the library so that imports resolve.
[[require]]
name = "cirlean"
path = "../cirlean-$CIR"

[[lean_lib]]
name = "EquivLean"
globs = ["EquivLean.+"]
EOF
rm -f "$EQDIR/lake-manifest.json"
"$VO_ROOT/scripts/run1.sh" -t 3600 -m 128 -c 2 -- bash -c "cd '$EQDIR' && lake build EquivLean.Core.Facts \
  EquivLean.Bridge.Cir.Tactic EquivLean.Bridge.Cir.Obs EquivLean.Bridge.Cir.AutoCouple EquivLean.Bridge.Cir.PtrArgs" \
  > "$VO_ROOT/runs/build_equivlean_$EQ7.log" 2>&1 || { echo "equiv-lean build failed: runs/build_equivlean_$EQ7.log" >&2; exit 1; }
echo "built $EQDIR against $CIRDIR"
[ $SWITCH -eq 1 ] || exit 0
cat > "$VO_ROOT/scripts/cert_pin.env.new" <<EOF
# The pins \`vo ci\` and \`vo patch\` use: equiv-lean (certificates, old ≡ new verdicts), the cirlean it is built
# against, and the scheduler's cirlean for the compared versions (the same one, so generated modules check in both
# packages). Sourced by scripts/vo when VO_CIRLEAN_DIR is not set. Change this file (only) when equiv-lean re-pins.
# Re-pinned by scripts/repin_equivlean.sh $EQ $CIR on $(date -u +%Y-%m-%dT%H:%M:%SZ).
VO_CIRLEAN_DIR="\$VO_ROOT/deps/cirlean-$CIR"
VO_CIRLEAN_PIN=$CIR
VO_CERT_CIRLEAN_DIR="\$VO_ROOT/deps/cirlean-$CIR"
VO_CERT_CIRLEAN_PIN=$CIR
VO_EQUIVLEAN_DIR="\$VO_ROOT/deps/equivlean-$EQ7"
VO_EQUIVLEAN_PIN=equivlean-$EQ7
EOF
cp -p "$VO_ROOT/scripts/cert_pin.env" "$VO_ROOT/scripts/cert_pin.env.before_$EQ7"
mv "$VO_ROOT/scripts/cert_pin.env.new" "$VO_ROOT/scripts/cert_pin.env"
echo "scripts/cert_pin.env now pins cirlean $CIR + equiv-lean $EQ7 (previous: scripts/cert_pin.env.before_$EQ7)"
SM="$VO_ROOT/scratch/prereg/repin_smoke_$EQ7"
mkdir -p "$SM"
for r in "scratch/core/cidemo.toml 1314c1f 5433813 abs_diff=equivalent,clamp_add=changed_only_where_old_unsafe,sign=behaviour_changed" \
         "scratch/core/cidemo.toml b88e74c 018ebeb get_or=equivalent,sum_arr=equivalent,swap=equivalent" \
         "targets/tiny_regex_c_lib.toml ef5deaeda453d314a454ca679678f0cfa4111910 74ceb765c75c20436b1c7e04631806527b91d7f9 (no recorded verdict)"; do
  set -- $r
  echo "== $1 $2..$3 expected: $4"
  VO_CI_RUN_DIR="$SM/$(basename "$1" .toml)" "$VO_ROOT/scripts/vo" ci "$VO_ROOT/$1" --base "$2" --head "$3" \
    --attempts 0 --budget 0 --check-timeout 600 > "$SM/$(basename "$1" .toml)_$2.log" 2>&1 || true
  grep -E "equivalence |blocked" "$SM/$(basename "$1" .toml)_$2.log" || echo "  (no verdict lines: see $SM)"
done
