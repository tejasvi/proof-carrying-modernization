#!/bin/bash
# Regenerate the CIR and the Lean modules of musl 1.2.5's generic C strlen and memcpy:
#   examples/cir/musl/{strlen,memcpy}.c  --clang -fclangir-->  {strlen,memcpy}.cir
#   --cir2lean-->  EquivLean/Demo/Cir/Musl/Gen/{Strlen,Memcpy}.lean
# (see README.md for the sources and the checks). Renamed to musl_strlen / musl_memcpy: under their
# own names cirlean's frontend would attach its strlen / memcpy models to them.
#   gen.sh MUSL_DIR SCRATCH_DIR
# MUSL_DIR: the extracted musl-1.2.5 tree; only its headers are read (include/, arch/x86_64/bits/,
# arch/generic/, src/include/, src/internal/). SCRATCH_DIR: a fresh directory for bits/alltypes.h and
# temporaries. Tools are used read-only: the upstream ClangIR build and the pinned cirlean's cir2lean.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../../.." && pwd)
MUSL=$1
S=$2
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
C2L=/home/user/equivlean_work/vendor/cirlean-28e2380/.lake/build/bin/cir2lean
mkdir -p "$S/obj/include/bits"
# musl's Makefile: sed -f tools/mkalltypes.sed arch/$ARCH/bits/alltypes.h.in include/alltypes.h.in
python3 -I "$D/mkalltypes.py" "$MUSL/arch/x86_64/bits/alltypes.h.in" "$MUSL/include/alltypes.h.in" \
  "$S/obj/include/bits/alltypes.h"
export TMPDIR=$S
ulimit -v 67108864
for f in strlen memcpy; do
  # musl's CFLAGS_ALL (Makefile): -std=c99 -nostdinc -ffreestanding -D_XOPEN_SOURCE=700 and its include order
  nice -n 10 "$TC/clang" -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering -O0 -std=c99 -nostdinc \
    -ffreestanding -D_XOPEN_SOURCE=700 -Dstrlen=musl_strlen -Dmemcpy=musl_memcpy \
    -I"$MUSL/arch/x86_64" -I"$MUSL/arch/generic" -I"$MUSL/src/include" -I"$MUSL/src/internal" \
    -I"$S/obj/include" -I"$MUSL/include" "$D/$f.c" -o "$D/$f.cir"
done
nice -n 10 "$C2L" "$D/strlen.cir" EquivLean.Demo.Cir.Musl.Gen.Strlen "$R/EquivLean/Demo/Cir/Musl/Gen/Strlen.lean"
nice -n 10 "$C2L" "$D/memcpy.cir" EquivLean.Demo.Cir.Musl.Gen.Memcpy "$R/EquivLean/Demo/Cir/Musl/Gen/Memcpy.lean"
