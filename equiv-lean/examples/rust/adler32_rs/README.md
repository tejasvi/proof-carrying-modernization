zlib's Adler-32 in safe Rust (R7). `src/lib.rs` was written by equiv-lean's agents (rusttrn, 2026-10-27)
in an Aeneas-friendly form from zlib v1.3.1's `adler32.c` (tag commit 51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf,
sha256 9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211), default configuration (no
`NO_DIVIDE`: `MOD`, `MOD28`, `MOD63` are `% BASE`), x86_64 LP64 types: `u64` for `uLong`, `usize` for
`z_size_t`, `u32` for `uInt`, `i64` for `z_off_t` and `z_off64_t`, `Option<&[u8]>` for `buf` (`None` is
`Z_NULL`). Functions: `adler32_z`, `adler32`, `adler32_combine`, `adler32_combine64` (and the private
`adler32_combine_`). No `unsafe`; `while` loops with no `return` inside. The unrolled `DO1`..`DO16` sums
are the helper `do_bytes`, which adds the same bytes in the same order; the paths and the reductions are
those of the C: one subtraction of `BASE` from each sum on the `len == 1` path, from `adler` on the
`len < 16` path (`sum2 % BASE` there), `% BASE` of both sums after each `NMAX` block and after the tail.
One case differs from the C: `buf == Z_NULL` with `len == 1`, where the C reads `buf[0]` (undefined
behaviour); the translation returns 1 there.

Differential test against the C (`difftest/`), re-runnable:

    bash difftest/run.sh OUT_DIR [SEED [N]]

It checks the sha256 of zlib's `adler32.c`, `zlib.h`, `zconf.h`, `zutil.h` (in `ZLIB_DIR`, default
`~/equivlean_work/dl/zlib-v1.3.1`), compiles the unmodified `adler32.c` with `gcc -O2` and links it with
`difftest/harness.c`, builds `difftest/drv` (path dependency on a copy of this crate) with
`cargo build --offline -j 1 --release` (overflow checks on; toolchain `RUST_TOOLCHAIN`, default 1.99.0,
`RUSTUP_AUTO_INSTALL=0`, `CARGO_NET_OFFLINE=true`), generates the cases with
`python3 -I difftest/gen_cases.py cases.bin SEED N`, runs both and compares the outputs (one line per
case: index, function, result), under `ulimit -v` 16 GiB and `nice -n 10`, writing only into `OUT_DIR`.
Cases: `adler32_z` and `adler32` on the lengths 0, 1, 2, 15, 16, 17, 5551, 5552, 5553, 11104, 11105 with
random, all-0xff and all-zero buffers and initial values with component sums below, at and above `BASE`;
a grid of `len == 1` and `len < 16` cases around `BASE`; `Z_NULL` with every length but 1; the combine
functions on negative, zero, `BASE`-adjacent and extreme `len2`; then N random cases.
Results (gcc 15.2.0, rustc/cargo 1.99.0): seed 20261027, N 20000: 27383 cases, all identical; seed 2,
N 200000: 207383 cases, all identical. Check of the test itself: with the single subtraction of `BASE`
from `sum2` on the `len == 1` path replaced by `% BASE` (a copy of the crate), 73 of the 27383 cases
(seed 20261027) differ and the script reports FAIL.

Extraction: Charon and Aeneas from ~/equivlean_work/dl/rel/aeneas_bin (Aeneas fdebf20), offline, toolchain
nightly-2026-09-17 (`RUSTUP_TOOLCHAIN`, `RUSTUP_AUTO_INSTALL=0`, `CARGO_NET_OFFLINE=true`), run on a copy of
this crate (`Cargo.toml`, `src/`): `charon cargo --preset=aeneas -- -j1` (gives `adler32_rs.llbc`, sha256
bd91226133d97a2318f38cd0e08a8c5cc206d55a9784d3890ebbbfb937b3ac64), then
`aeneas -backend lean -split-files -subdir EquivLean/Demo/Gen/Aeneas/Adler32Rs -dest <out> adler32_rs.llbc`
(gives `EquivLean/Demo/Gen/Aeneas/Adler32Rs/{Types,Funs}.lean`, copied unchanged).
