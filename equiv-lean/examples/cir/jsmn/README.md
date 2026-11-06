# jsmn (C) for equiv-lean's R5 port: the C side's source and ClangIR

## Sources

- `jsmn.h` is jsmn's header from zserge/jsmn at commit `25647e692c7906b96ffd2b05ca54c097948e879c`, byte for byte (sha256 `c04533e9181e1e33baceb0f55ac449b05145bb936e8c68cc77dfe0d8277514fb`), copied from `~/veriforch/targets/jsmn`, a checkout of that commit. `LICENSE` is jsmn's licence (MIT).
- `jsmn_run.c` is the run harness. It is not part of jsmn. It defines `JSMN_STATIC`, includes `jsmn.h` in jsmn's default configuration (neither `JSMN_PARENT_LINKS` nor `JSMN_STRICT`), and defines `jsmn_run(parser, js, len, tokens, num_tokens)`. That function calls `jsmn_init(parser)` and then `jsmn_parse(parser, js, len, tokens, num_tokens)` once.
- The harness is needed because, with `JSMN_STATIC`, `jsmn_init` and `jsmn_parse` have internal linkage, and clang emits such functions only when something calls them.

## Generation (`gen.sh`)

- `clang` is the pinned upstream ClangIR build (`~/cirlean_work/toolchain/upstream-4955d32b`):

      clang -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering -O0 jsmn_run.c -o jsmn_run.cir

- `cir2lean` comes from the pinned cirlean copy (`~/equivlean_work/vendor/cirlean-28e2380`):

      cir2lean jsmn_run.cir EquivLean.Demo.Gen.Cir.Jsmn.Jsmn EquivLean/Demo/Gen/Cir/Jsmn/Jsmn.lean

- The module has 7 functions, all with bodies: `jsmn_alloc_token`, `jsmn_fill_token`, `jsmn_parse_primitive`, `jsmn_parse_string`, `jsmn_parse`, `jsmn_init` and `jsmn_run`. It also has 2 records (`jsmntok`, `jsmn_parser`), no globals, and 1159 operations.

## Punning scan

`~/equivlean_work/scratch/main/punscan_v1.py` flags pointer casts between scalar types of different widths (cirlean ≤ 28e2380 gives such accesses a one-element meaning instead of UB). On `jsmn_run.cir` it finds 11 bitcasts. All 11 are `!cir.ptr<!void> -> !cir.ptr<!rec_jsmntok>` of the null pointer constant, from jsmn's `tokens == NULL` and `token == NULL` tests. None is a cast between scalar pointer types of different widths (0 hits).
