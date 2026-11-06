#!/usr/bin/env bash
# PREREG_C1b launch, once the equiv-lean maintainer session has an equiv-lean commit whose Cir bridge builds on cirlean bd8614f:
#   scripts/prereg_c1b_launch.sh EQSHA
# 1. equiv-lean EQSHA cloned (read-only source ~/equivlean) into deps/equivlean-<sha7>-cir-bd8614f, lakefile pointing at
#    ../cirlean-bd8614f, certificate modules built;
# 2. runs/prereg/C1b/cert_pin_c1b.env written from the template (cirlean bd8614f + that equiv-lean);
# 3. smoke tests from the live tree on cidemo pairs outside the selected set; any verdict other than the recorded one
#    stops here;
# 4. frozen copy ~/veriforch_frozen/C1b_<UTC> (scripts/freeze_copy.sh) and ONE real step from it (cidemo
#    b88e74c..018ebeb); a wrong verdict stops here;
# 5. the build-fix record goes into runs/prereg/C1b/pins.json (key c1b_buildfix), then the driver starts under nohup
#    from the frozen copy and records its own pins (key c1b).
set -eu
VO=/home/user/veriforch
EQ="${1:?usage: prereg_c1b_launch.sh EQUIVLEAN_SHA}"
EQ7="${EQ:0:7}"
C1B=$VO/runs/prereg/C1b
CIR=$VO/deps/cirlean-bd8614f
EQDIR=$VO/deps/equivlean-$EQ7-cir-bd8614f
[ -x "$CIR/.lake/build/bin/cir2lean" ] || { echo "no built cirlean at $CIR" >&2; exit 2; }
case "$(git -C "$CIR" rev-parse HEAD)" in bd8614f*) ;; *) echo "$CIR is not at bd8614f" >&2; exit 2 ;; esac
# 1. equiv-lean
if [ ! -d "$EQDIR" ]; then git clone -q "$HOME/equivlean" "$EQDIR"; git -C "$EQDIR" checkout -q "$EQ"; fi
case "$(git -C "$EQDIR" rev-parse HEAD)" in "$EQ"*) ;; *) echo "$EQDIR is not at $EQ" >&2; exit 2 ;; esac
cat > "$EQDIR/lakefile.toml" <<EOT
name = "equivlean"
version = "0.1.0"
defaultTargets = ["EquivLean"]

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

# veriforch's pinned copy of equiv-lean ($EQ) for PREREG_C1b, built against deps/cirlean-bd8614f.
[[require]]
name = "cirlean"
path = "../cirlean-bd8614f"

[[lean_lib]]
name = "EquivLean"
globs = ["EquivLean.+"]
EOT
rm -f "$EQDIR/lake-manifest.json"
"$VO/scripts/run1.sh" -t 3600 -m 128 -c 2 -- bash -c "cd '$EQDIR' && lake build EquivLean.Core.Facts \
  EquivLean.Bridge.Cir.Tactic EquivLean.Bridge.Cir.Obs EquivLean.Bridge.Cir.AutoCouple EquivLean.Bridge.Cir.PtrArgs" \
  > "$C1B/build_equivlean_${EQ7}_bd8614f.log" 2>&1 || { echo "equiv-lean build failed: $C1B/build_equivlean_${EQ7}_bd8614f.log" >&2; exit 1; }
echo "built $EQDIR"
# 2. pin file
sed "s/EQSHA/$EQ7/g" "$C1B/cert_pin_c1b.env.template" > "$C1B/cert_pin_c1b.env"
export VO_CERT_PIN_ENV="$C1B/cert_pin_c1b.env"
# 3. smoke tests (live tree)
SM=$C1B/smoke_$(date -u +%Y%m%dT%H%M%SZ); mkdir -p "$SM"
check() {   # tree target base head expected...
  local tree=$1 tgt=$2 b=$3 h=$4; shift 4
  VO_CI_RUN_DIR="$SM/$(basename "$tree")_$b" "$tree/scripts/vo" ci "$tree/$tgt" --base "$b" --head "$h" \
    --attempts 0 --budget 0 --check-timeout 600 > "$SM/$(basename "$tree")_$b.log" 2>&1 || true
  local ok=1
  for e in "$@"; do
    command grep -q "equivalence ${e%%=*}: ${e#*=}" "$SM/$(basename "$tree")_$b.log" || { echo "smoke FAIL: $e ($SM/$(basename "$tree")_$b.log)"; ok=0; }
  done
  [ $ok = 1 ] && echo "smoke OK: $b..$h $*"
  return $((1 - ok))
}
check "$VO" scratch/core/cidemo.toml 1314c1f 5433813 abs_diff=equivalent clamp_add=changed_only_where_old_unsafe sign=behaviour_changed
check "$VO" scratch/core/cidemo.toml b88e74c 018ebeb get_or=equivalent sum_arr=equivalent swap=equivalent
# 4. frozen copy and one real step from it
F=$HOME/veriforch_frozen/C1b_$(date -u +%Y%m%dT%H%M%SZ)
"$VO/scripts/freeze_copy.sh" "$F"
check "$F" scratch/core/cidemo.toml b88e74c 018ebeb get_or=equivalent sum_arr=equivalent swap=equivalent
echo "$F" > "$C1B/frozen_path.txt"
# the changes since C1's pins (PREREG_C1b "Tool pins"): veriforch (frozen copy diff), cirlean and equiv-lean logs
diff -ru -x deps -x runs -x scratch -x .venv -x SHA256SUMS "$HOME/veriforch_frozen/C_20261024T142304Z" "$F" \
  > "$C1B/changes_veriforch_since_C1.diff" || true
git -C "$CIR" log --oneline 88e6008..bd8614f > "$C1B/changes_cirlean_88e6008..bd8614f.txt"
git -C "$EQDIR" log --oneline 99b598e.."$EQ" > "$C1B/changes_equivlean_99b598e..$EQ7.txt" || true
# 5. build-fix record, then the driver
python3 - "$C1B" <<'EOT'
import hashlib, json, sys, time
from pathlib import Path
c1b = Path(sys.argv[1]); p = c1b / "pins.json"
allp = json.loads(p.read_text()) if p.exists() else {}
if "c1b" in allp:
    raise SystemExit("pins.json already has c1b pins (a run started)")
vo = Path("/home/user/veriforch")
allp["c1b_buildfix"] = {
    "recorded": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "diff": str(c1b / "buildfix.diff"),
    "diff_sha256": hashlib.sha256((c1b / "buildfix.diff").read_bytes()).hexdigest(),
    "target": "targets/cjson_lib_c1b_buildfix.toml",
    "target_sha256": hashlib.sha256((vo / "targets/cjson_lib_c1b_buildfix.toml").read_bytes()).hexdigest(),
    "flags_added": ["-Wno-error=int-conversion", "-D_ISOC99_SOURCE"],
    "orders": [12, 14, 27, 46, 48, 53, 55], "note": str(c1b / "BUILDFIX.md")}
p.write_text(json.dumps(allp, indent=1))
print("build fix recorded in", p)
EOT
date -u +%Y-%m-%dT%H:%M:%SZ > "$C1B/start_time.txt"
cd "$VO"
nohup "$F/scripts/prereg_c1b.sh" --frozen "$F" --workers 6 >> "$C1B/c1b_driver.log" 2>&1 &
echo "C1b started $(cat "$C1B/start_time.txt") from $F (manifest $(sha256sum "$F/SHA256SUMS" | cut -c1-64)), driver pid $!"
