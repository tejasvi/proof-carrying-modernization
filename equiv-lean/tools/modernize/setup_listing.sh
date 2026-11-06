#!/bin/bash
# Headline A: set up a record-listing program (one input file, every record DISPLAYed, like
# CBACT02C) from its imported translations: Java/Rust Gen modules, the generated statements
# (genstmt.py) and the proof scaffolding instantiated from CBACT02C's (only names and sizes change).
#   tools/modernize/setup_listing.sh <prog> <RecordClass> <FdCamel> <recLen> <memSize> <thm>
#   e.g. tools/modernize/setup_listing.sh cbact03c CardXrefRecord XreffileFile 50 123 cbact03c_lists
set -eu
p=$1; RC=$2; FD=$3; RL=$4; MS=$5; THM=$6
P=$(echo $p | sed 's/^./\U&/'); U=$(echo $p | tr a-z A-Z)
R=/home/user/equivlean; cd $R
M=$HOME/veriforch/runs/modernize/$U
D=EquivLean/Modernize/$P
mkdir -p $D
rc=$(echo $RC | sed 's/^./\L&/')
cat > $D/JavaGen.lean <<EOT
import Jimple

/-!
Generated input: Soot 4.7.1 Jimple (\`mod_$p/*.jimple\`) of \`examples/java/mod_$p/$P.java\`,
veriforch's guided Java translation of CardDemo's $U (runs/modernize/$U, versions.json), compiled
by \`javac --release 17\` (\`examples/java/build_jimple.sh mod_$p\`).  The path is relative to the
repository root.
-/

jimple_import "EquivLean/Demo/Gen/Jimple/mod_$p" as EquivLean.Modernize.$P.Java.Gen
EOT
for lang in java rust; do
  if [ $lang = java ]; then gm=EquivLean.Modernize.$P.JavaGen; out=$D/JavaStatement.lean; ns=Java; jd="--jimple-dir EquivLean/Demo/Gen/Jimple/mod_$p"
  else gm=EquivLean.Demo.Gen.Aeneas.Mod$P.Funs; out=$D/RustStatement.lean; ns=Rust; jd=""; fi
  python3 tools/modernize/genstmt.py --mapping $M/mapping.json --lang $lang \
    --ir-rel "../../../examples/cobol/carddemo/$p.ir.json" --mem-rel init_mem.hex \
    --cobol-module EquivLean.Demo.Cobol.$P.Prog --cobol-prog CardDemo.$P \
    --cobol-thm-file EquivLean/Demo/Cobol/$P/Prog.lean --cobol-thm $THM \
    --gen-module $gm --namespace EquivLean.Modernize.$P.$ns $jd -o $out
done
for f in JavaProof RustProof; do
  sed -e "s/Cbact02c\\\$CardRecord/$P\$$RC/g" -e "s/Cbact02c/$P/g" -e "s/cbact02c_lists/$THM/g" \
      -e "s/cbact02c/$p/g" -e "s/CardfileFile/$FD/g" -e "s/cardRecord_/${rc}_/g" \
      -e "s/CardRecord/$RC/g" -e "s/CBACT02C/$U/g" -e "s/initMem.size = 323/initMem.size = $MS/" \
      -e "s/r.length = 150/r.length = $RL/" EquivLean/Modernize/Cbact02c/$f.lean > $D/$f.lean
done
echo "set up $D"
