#!/bin/bash
# Regenerate the CIR and the Lean module of zlib's adler32.c (madler/zlib v1.3.1, tag commit 51b7f2a, adler32.c,
# zlib.h, zconf.h, zutil.h and LICENSE copied here byte for byte):
#   examples/cir/zlib_adler32/adler32.c  --clang -fclangir-->  adler32.cir  --cir2lean-->
#   EquivLean/Demo/Gen/Cir/Adler32/Adler32.lean
# The defines are zlib's own for adler32.o: its configure, on Linux with gcc, sets
# CFLAGS="-O3 -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN" (configure l.199, l.525-527, l.830 at 51b7f2a), and
# Makefile.in compiles `$(CC) $(CFLAGS) $(ZINC) -c -o adler32.o adler32.c` (l.155-156). The one deviation: -O0
# instead of -O3, as for the other ClangIR inputs (jsmn, musl), so that ClangIR shows the source's operations.
# configure also turns zconf.h's `#ifdef HAVE_UNISTD_H` into `#if 1`; zconf.h l.477-479 defines Z_HAVE_UNISTD_H
# itself under _LARGEFILE64_SOURCE, so the shipped zconf.h is used unmodified.
# Tools are used read-only: the upstream ClangIR build and the cir2lean executable of the pinned cirlean copy.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../../.." && pwd)
W=/home/user/equivlean_work
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
C2L=$W/vendor/cirlean-28e2380/.lake/build/bin/cir2lean
export TMPDIR=${TMPDIR:-$W/scratch/eq-cir/r7/tmp}
mkdir -p "$TMPDIR" "$R/EquivLean/Demo/Gen/Cir/Adler32"
ulimit -v 67108864
nice -n 10 "$TC/clang" -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering -O0 \
  -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN -I "$D" "$D/adler32.c" -o "$D/adler32.cir"
nice -n 10 "$C2L" "$D/adler32.cir" EquivLean.Demo.Gen.Cir.Adler32.Adler32 \
  "$R/EquivLean/Demo/Gen/Cir/Adler32/Adler32.lean"
