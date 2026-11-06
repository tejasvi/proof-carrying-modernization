#!/bin/bash
# Native differential test: zlib 1.3.1's adler32.c (unmodified, gcc -O2) against the safe Rust
# translation examples/rust/adler32_rs (cargo --release, overflow checks on).
#
#   bash run.sh OUT_DIR [SEED [N]]
#
# OUT_DIR: a new or empty directory; the build, the case file and both outputs go there and
# nowhere else.  SEED (default 20261027) and N (random cases, default 20000) go to gen_cases.py.
# Environment: ZLIB_DIR (default ~/equivlean_work/dl/zlib-v1.3.1; adler32.c, zlib.h, zconf.h and
# zutil.h of v1.3.1, checked by sha256), RUST_TOOLCHAIN (default 1.99.0-x86_64-unknown-linux-gnu).
# Offline (RUSTUP_AUTO_INSTALL=0, CARGO_NET_OFFLINE=true), one job, ulimit -v 16 GiB, nice 10.
# Prints the tool versions, the seed, the case count, PASS counts per function and ALL PASS when
# the two outputs are identical (exit 0), FAIL otherwise (exit 1).
set -euo pipefail
OUT=${1:?usage: bash run.sh OUT_DIR [SEED [N]]}
SEED=${2:-20261027}
N=${3:-20000}
HERE=$(cd "$(dirname "$0")" && pwd)
CRATE=$(cd "$HERE/.." && pwd)
ZLIB_DIR=${ZLIB_DIR:-$HOME/equivlean_work/dl/zlib-v1.3.1}
TC=${RUST_TOOLCHAIN:-1.99.0-x86_64-unknown-linux-gnu}
ulimit -v 16777216
mkdir -p "$OUT"
if [ -n "$(ls -A "$OUT")" ]; then
  echo "OUT_DIR $OUT is not empty"
  exit 2
fi
OUT=$(cd "$OUT" && pwd)
echo "seed $SEED, N $N"

# the unmodified zlib 1.3.1 sources
check() {
  if ! echo "$2  $ZLIB_DIR/$1" | sha256sum -c --quiet -; then
    echo "sha256 mismatch: $ZLIB_DIR/$1"
    exit 2
  fi
}
check adler32.c 9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211
check zlib.h 8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c
check zconf.h f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae
check zutil.h dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea
echo "zlib sources: $ZLIB_DIR (sha256 checked)"

# C: adler32.c as is, -O2, and the harness
gcc --version | head -1
nice -n 10 gcc -O2 -I"$ZLIB_DIR" -c "$ZLIB_DIR/adler32.c" -o "$OUT/adler32.o"
nice -n 10 gcc -O2 -Wall -I"$ZLIB_DIR" "$HERE/harness.c" "$OUT/adler32.o" -o "$OUT/c_harness"

# Rust: copies of the crate and the driver, built offline in OUT_DIR
mkdir -p "$OUT/src/adler32_rs" "$OUT/src/drv"
cp -L "$CRATE/Cargo.toml" "$OUT/src/adler32_rs/"
cp -rL "$CRATE/src" "$OUT/src/adler32_rs/"
cp -L "$HERE/drv/Cargo.toml" "$OUT/src/drv/"
cp -rL "$HERE/drv/src" "$OUT/src/drv/"
if [ -n "$(find "$OUT/src" -type l)" ]; then
  echo "symbolic link in the copy"
  exit 2
fi
export RUSTUP_TOOLCHAIN=$TC RUSTUP_AUTO_INSTALL=0 CARGO_NET_OFFLINE=true
export CARGO_HOME="$OUT/cargo_home" CARGO_TARGET_DIR="$OUT/target"
rustc --version
cargo --version
nice -n 10 cargo build --offline -j 1 --release --manifest-path "$OUT/src/drv/Cargo.toml"

# the cases and the two runs
nice -n 10 python3 -I "$HERE/gen_cases.py" "$OUT/cases.bin" "$SEED" "$N"
sha256sum "$OUT/cases.bin"
nice -n 10 "$OUT/c_harness" "$OUT/cases.bin" > "$OUT/c.txt"
nice -n 10 "$OUT/target/release/adler32_drv" "$OUT/cases.bin" > "$OUT/rust.txt"

# comparison, per function
paste -d ' ' "$OUT/c.txt" "$OUT/rust.txt" | awk '
  { k = $2; n[k]++; if ($1 == $4 && $2 == $5 && $3 == $6) ok[k]++ }
  END {
    split("adler32_z adler32 adler32_combine adler32_combine64", name, " ")
    for (k = 0; k < 4; k++) printf "%-18s %d/%d PASS\n", name[k + 1], ok[k] + 0, n[k] + 0
  }'
if [ "$(wc -l < "$OUT/c.txt")" -gt 0 ] && cmp -s "$OUT/c.txt" "$OUT/rust.txt"; then
  echo "ALL PASS: $(wc -l < "$OUT/c.txt") cases, outputs identical"
else
  echo "FAIL: the outputs differ"
  exit 1
fi
