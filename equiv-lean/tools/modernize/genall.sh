#!/bin/bash
# Headline A: regenerate every generated statement (EquivLean/Modernize/<Prog>/{Java,Rust}Statement.lean)
# from veriforch's mapping.json, coblean's IR and theorem, and the harness storage.  The table below
# is the whole per-program input of the generator; `git diff` after a run shows any change.
#   tools/modernize/genall.sh [prog…]      (default: every program in the table)
set -eu
# the repository this script is in (a worktree regenerates its own files)
R=$(cd "$(dirname "$0")/../.." && pwd); cd $R
# prog | coblean theorem | file of the theorem (under EquivLean/Demo/Cobol/<Prog>/) | extra genstmt options
#   | languages (default: java rust) | variant (optional: a second statement in EquivLean/Modernize/<Prog>/<variant>/)
TABLE='
cbact02c|cbact02c_lists|Prog.lean|
cbact03c|cbact03c_lists|Prog.lean|
cbcus01c|cbcus01c_lists|Prog.lean|
cbtrn01c|cbtrn01c_verifies_all|Prog.lean|
cbact04c|cbact04c_all|All.lean|--rust-crate cbact04c_t --ksds --domain EquivLean.Modernize.Cbact04c.Domain --domain-module EquivLean.Modernize.Cbact04c.Domain
cbact04c|cbact04c_every|Every.lean|--rust-crate cbact04c_t --domain EquivLean.Modernize.Cbact04c.Every.Domain --domain-module EquivLean.Modernize.Cbact04c.Every.Domain||Every
cbtrn02c|cbtrn02c_posts|Prog.lean|--domain EquivLean.Modernize.Cbtrn02c.Domain --domain-module EquivLean.Modernize.Cbtrn02c.Domain
cbtrn02c|cbtrn02c_any|Dup.lean|--domain EquivLean.Modernize.Cbtrn02c.Any.Domain --domain-module EquivLean.Modernize.Cbtrn02c.Any.Domain||Any
cbact01c|cbact01c_extracts|Prog.lean|
cbtrn03c|cbtrn03c_every|Every.lean|--domain EquivLean.Modernize.Cbtrn03c.Domain --domain-module EquivLean.Modernize.Cbtrn03c.Domain
cbstm03b|cbstm03b_call|Prog.lean|--subprogram --domain EquivLean.Modernize.Cbstm03b.Domain --domain-module EquivLean.Modernize.Cbstm03b.Domain
cbstm03a|stm_run_sorted|StmCore/Sorted.lean|--ir-rel ../../../examples/cobol/carddemo/cbstm03ab.ir.json --cobol-module EquivLean.Demo.Cobol.Cbstm03a.Stm.WalkSummary --cobol-prog Cobol.Stm.Stm --domain EquivLean.Modernize.Cbstm03a.Domain --domain-module EquivLean.Modernize.Cbstm03a.Domain
'
want=" $* "
echo "$TABLE" | while IFS='|' read -r p thm tf extra langs variant; do
  [ -n "$p" ] || continue
  if [ $# -gt 0 ] && [[ "$want" != *" $p "* ]]; then continue; fi
  P=$(echo $p | sed 's/^./\U&/'); U=$(echo $p | tr a-z A-Z)
  M=$HOME/veriforch/runs/modernize/$U
  D=EquivLean/Modernize/$P; NS=EquivLean.Modernize.$P; up=""
  if [ -n "$variant" ]; then
    # a second statement of the same program (another COBOL theorem / domain), in its own subdirectory
    D=$D/$variant; NS=$NS.$variant; up="../"
  fi
  for lang in ${langs:-java rust}; do
    if [ $lang = java ]; then gm=EquivLean.Modernize.$P.JavaGen; out=$D/JavaStatement.lean; ns=Java
      jd="--jimple-dir EquivLean/Demo/Gen/Jimple/mod_$p"
      [ -n "$variant" ] && jd="$jd --gen-ns EquivLean.Modernize.$P.Java.Gen"
    else gm=EquivLean.Demo.Gen.Aeneas.Mod$P.Funs; out=$D/RustStatement.lean; ns=Rust; jd=""; fi
    mkdir -p $D
    # shellcheck disable=SC2086
    python3 tools/modernize/genstmt.py --mapping $M/mapping.json --lang $lang \
      --ir-rel "${up}../../../examples/cobol/carddemo/$p.ir.json" --mem-rel ${up}init_mem.hex \
      --cobol-module EquivLean.Demo.Cobol.$P.Prog --cobol-prog CardDemo.$P \
      --cobol-thm-file EquivLean/Demo/Cobol/$P/$tf --cobol-thm $thm \
      --gen-module $gm --namespace $NS.$ns $jd $extra -o $out
  done
  echo "generated $D/{Java,Rust}Statement.lean"
done
