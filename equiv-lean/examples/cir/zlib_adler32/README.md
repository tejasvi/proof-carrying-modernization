# zlib adler32 (C) for equiv-lean's R7 port: the C side's source and ClangIR

## Sources

- `adler32.c`, `zlib.h`, `zconf.h`, `zutil.h` and `LICENSE` are zlib v1.3.1's files at tag commit
  `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf`, byte for byte, copied from `~/equivlean_work/dl/zlib-v1.3.1`
  (sha256: `adler32.c` `9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211`, `zlib.h`
  `8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c`, `zconf.h`
  `f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae`, `zutil.h`
  `dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea`, `LICENSE`
  `845efc77857d485d91fb3e0b884aaa929368c717ae8186b66fe1ed2495753243`).
- No harness is needed: `adler32_z`, `adler32`, `adler32_combine` and `adler32_combine64` have external linkage,
  so clang emits them (and the `local` helper `adler32_combine_` they call).

## Generation (`gen.sh`)

- The defines are zlib's own for `adler32.o`. Its `configure` (at 51b7f2a), on Linux with gcc, sets
  `CFLAGS="-O3 -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN"` (l.199, l.525-527, l.830), and `Makefile.in` compiles
  `$(CC) $(CFLAGS) $(ZINC) -c -o adler32.o adler32.c` (l.155-156). `configure` also turns `zconf.h`'s
  `#ifdef HAVE_UNISTD_H` into `#if 1`; `zconf.h` l.477-479 defines `Z_HAVE_UNISTD_H` itself when
  `_LARGEFILE64_SOURCE` is set, so the shipped `zconf.h` is used unmodified.
- The one deviation from zlib's build is `-O0` for the ClangIR front end instead of `-O3`, as for jsmn and musl:
  ClangIR then shows the source's operations one by one.
- `clang` is the pinned upstream ClangIR build (`~/cirlean_work/toolchain/upstream-4955d32b`):

      clang -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering -O0 -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN \
        -I . adler32.c -o adler32.cir

- `cir2lean` comes from the pinned cirlean copy (`~/equivlean_work/vendor/cirlean-28e2380`):

      cir2lean adler32.cir EquivLean.Demo.Gen.Cir.Adler32.Adler32 EquivLean/Demo/Gen/Cir/Adler32/Adler32.lean

- The module has 5 functions, all with bodies (`adler32_z`, `adler32`, `adler32_combine`, `adler32_combine_`,
  `adler32_combine64`), no records, no globals and 914 operations. On LP64, `uLong` and `z_size_t` are
  `!u64i`, `Bytef*` is `!cir.ptr<!u8i>`, `uInt` is `!u32i`, `z_off_t` and `z_off64_t` are `!s64i`.

## Punning scan

`~/equivlean_work/scratch/main/punscan_v1.py` flags pointer casts between scalar types of different widths
(cirlean ≤ 28e2380 gives such accesses a one-element meaning instead of UB). `adler32.cir` has no bitcast at all
(0 bitcast lines, 0 hits).
