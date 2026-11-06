#!/usr/bin/env bash
# PREREG_T_v1 T3: start the real run, after main's GO, from the frozen copy whose final dry run passed
# (notes/thrift/T3_DRIVER.md). The driver records its pins in runs/prereg/T3/pins.json and refuses to start when that
# file exists (a run already started: resume with the same command plus --resume, after a crash fix from a new copy).
#
#   scripts/prereg_t3_launch.sh FROZEN_DIR [WORKERS (default 12: main 10-25, each start gated by the 1-min load <= 450 and
#   >= 150 GB free; T2's 12 guaranteed slots come first)]
set -eu
VO=/home/user/veriforch
F="${1:?usage: prereg_t3_launch.sh FROZEN_DIR [WORKERS]}"
W="${2:-12}"
IN="$VO/runs/prereg/T3_inputs"
(cd "$F" && sha256sum --check --strict --quiet SHA256SUMS) || { echo "frozen copy $F does not match its manifest" >&2; exit 2; }
[ -f "$F/scripts/prereg_t3.py" ] || { echo "no scripts/prereg_t3.py in $F" >&2; exit 2; }
[ ! -e "$VO/runs/prereg/T3/pins.json" ] || { echo "runs/prereg/T3/pins.json exists: a run already started" >&2; exit 2; }
for f in "$IN/cert_pin_t3_v2.env" "$IN/java_jarsets.tsv" "$IN/rust/sets.json"; do
  [ -f "$f" ] || { echo "missing input $f" >&2; exit 2; }
done
mkdir -p "$VO/runs/prereg/T3"
date -u +%Y-%m-%dT%H:%M:%SZ > "$VO/runs/prereg/T3/start_time.txt"
echo "$F" > "$VO/runs/prereg/T3/frozen_path.txt"
cd "$VO"
nohup "$VO/scripts/run1.sh" -t 172800 -m 256 -c 800 -l "$VO/runs/prereg/T3.guard.log" -- \
  "$F/.venv/bin/python" -B "$F/scripts/prereg_t3.py" --frozen "$F" --pins "$IN/cert_pin_t3_v2.env" \
  --java-jarsets "$IN/java_jarsets.tsv" --rust-depsets "$IN/rust" --workers "$W" --shared-caches all \
  --blocked-verdicts skip \
  >> "$VO/runs/prereg/T3/t3_driver.log" 2>&1 &
echo "T3 started $(cat "$VO/runs/prereg/T3/start_time.txt") from $F (manifest $(sha256sum "$F/SHA256SUMS" | cut -c1-64)), run1.sh wrapper pid $!"
