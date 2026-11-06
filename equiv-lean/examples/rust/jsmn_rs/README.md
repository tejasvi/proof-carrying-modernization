jsmn in safe Rust (R5). `src/lib.rs` was written by equiv-lean's agents (rusttrn, 2026-10-26) in an
Aeneas-friendly form from jsmn.h at zserge/jsmn 25647e6 (sha256 c04533e9181e1e33baceb0f55ac449b05145bb936e8c68cc77dfe0d8277514fb),
default configuration (neither `JSMN_PARENT_LINKS` nor `JSMN_STRICT`), the mode with a token array only.
No `unsafe`; loops are `while` loops with state flags (no `return` inside a loop); the token array is
`&mut [JsmnTok]`; the source length is `js.len()` and the token capacity `tokens.len()`; positions and
the token counter are `usize` (C: `unsigned int`), token fields and `toksuper` `i32` (C: `int`).
The backward searches of the closing-bracket and comma cases are the functions `find_open` and
`find_open_container`.

Differential test against the C (`difftest/`):
- C: `gcc -O1 -std=c99 -Wall -I<dir with jsmn.h> -o harness difftest/harness.c` (gcc 15.2.0, `JSMN_STATIC`).
- Rust: `difftest/drv` (path dependency on this crate), `cargo build --offline -j 1 --release` with
  rustc/cargo 1.99.0, `RUSTUP_AUTO_INSTALL=0 CARGO_NET_OFFLINE=true`.
- Inputs: `python3 -I difftest/gen_cases.py <jsmn>/test/tests.c cases.bin <N> <seed>`: the 39 `parse(...)` calls
  of jsmn's test/tests.c with their token count and with 0, 1, 2, 3, 5, 8, 16, 100 tokens; the 385 string
  literals of tests.c with 0, 1, 4, 16, 256 tokens; N random documents (valid JSON, mutated JSON with NUL
  and non-ASCII bytes, truncated JSON) with random token counts.
- Both programs print, per case, the return value and the first min(max(ret, 0), num_tokens) tokens
  (type, start, end, size). Seed 1, N = 30000: 32245 cases; seed 2, N = 200000: 202245 cases; the C
  and Rust outputs are identical (cmp) in both runs.

Extraction: Charon and Aeneas from ~/equivlean_work/dl/rel/aeneas_bin (Aeneas fdebf20), offline, toolchain
nightly-2026-09-17 (`RUSTUP_TOOLCHAIN`, `RUSTUP_AUTO_INSTALL=0`, `CARGO_NET_OFFLINE=true`):
`charon cargo --preset=aeneas -- -j1` (gives `jsmn_rs.llbc`), then
`aeneas -backend lean -split-files -subdir EquivLean/Demo/Gen/Aeneas/JsmnRs -dest <out> jsmn_rs.llbc`
(gives `EquivLean/Demo/Gen/Aeneas/JsmnRs/{Types,Funs}.lean`, copied unchanged).
