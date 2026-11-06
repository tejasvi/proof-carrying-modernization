#!/bin/bash
# Regenerate the CIR and the Lean module of jsmn (zserge/jsmn @ 25647e6, jsmn.h copied here with LICENSE) with
# the run harness jsmn_run.c:
#   examples/cir/jsmn/jsmn_run.c  --clang -fclangir-->  jsmn_run.cir  --cir2lean-->  EquivLean/Demo/Gen/Cir/Jsmn/Jsmn.lean
# Tools are used read-only: the upstream ClangIR build and the cir2lean executable of the pinned cirlean copy.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../../.." && pwd)
W=/home/user/equivlean_work
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
C2L=$W/vendor/cirlean-28e2380/.lake/build/bin/cir2lean
export TMPDIR=${TMPDIR:-$W/scratch/cir-repin/jsmn/tmp}
mkdir -p "$TMPDIR" "$R/EquivLean/Demo/Gen/Cir/Jsmn"
ulimit -v 67108864
nice -n 10 "$TC/clang" -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering -O0 "$D/jsmn_run.c" \
  -o "$D/jsmn_run.cir"
nice -n 10 "$C2L" "$D/jsmn_run.cir" EquivLean.Demo.Gen.Cir.Jsmn.Jsmn "$R/EquivLean/Demo/Gen/Cir/Jsmn/Jsmn.lean"
