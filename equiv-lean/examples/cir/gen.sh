#!/bin/bash
# Regenerate the CIR and the Lean modules of the C++ demos:
#   examples/cir/X.cpp  --clang -fclangir-->  examples/cir/X.cir  --cir2lean-->  EquivLean/Demo/Gen/Cir/<X>.lean
# Tools are used read-only: the upstream ClangIR build and the cir2lean executable of the pinned cirlean copy.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../.." && pwd)
W=/home/user/equivlean_work
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
CX=/home/user/cirlean_work/dl_cir2c_eb2a332/cir2c-eb2a332/libcxx/include/c++/v1
C2L=$W/vendor/cirlean-28e2380/.lake/build/bin/cir2lean
export TMPDIR=${TMPDIR:-$W/scratch/eq-cir/tmp}
mkdir -p "$TMPDIR" "$R/EquivLean/Demo/Gen/Cir"
ulimit -v 67108864
for x in a_old a_new b_old b_new c_old c_new e_old e_new v_old v_new m_old m_new cb_old cb_new bd_old bd_new p_old p_new; do
  mod=$(echo "$x" | sed -E 's/(^|_)([a-z])/\U\2/g')   # a_old -> AOld
  nice -n 10 "$TC/clang++" -std=c++20 -nostdinc++ -isystem "$CX" -fclangir -emit-cir \
    -Xclang -fno-clangir-call-conv-lowering "$D/$x.cpp" -o "$D/$x.cir"
  nice -n 10 "$C2L" "$D/$x.cir" "EquivLean.Demo.Gen.Cir.$mod" "$R/EquivLean/Demo/Gen/Cir/$mod.lean"
done
