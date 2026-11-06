#!/bin/bash
# Regenerate the CIR and the Lean module of tiny-regex-c's re.c (kokke/tiny-regex-c @ f2632c6, copied
# here with re.h and LICENSE):
#   examples/cir/tinyregex/re.c  --clang -fclangir-->  re.cir  --cir2lean-->  EquivLean/Demo/Gen/Cir/TinyRegex.lean
# Tools are used read-only: the upstream ClangIR build and the cir2lean executable of the pinned cirlean copy.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../../.." && pwd)
W=/home/user/equivlean_work
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
C2L=$W/vendor/cirlean-ec40522/.lake/build/bin/cir2lean
export TMPDIR=${TMPDIR:-$W/scratch/cir-repin/trx/tmp}
ulimit -v 67108864
nice -n 10 "$TC/clang" -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering "$D/re.c" -o "$D/re.cir"
nice -n 10 "$C2L" "$D/re.cir" EquivLean.Demo.Gen.Cir.TinyRegex "$R/EquivLean/Demo/Gen/Cir/TinyRegex.lean"
