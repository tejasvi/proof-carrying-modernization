/-
# `stm_auto`: symbolic execution for the CBSTM03A+B phase lemmas

`cobol_auto` with the control-flow rewrites `stm_flow` and the numeric `MOVE` lemma of
`EquivLean.Demo.Cobol.Cbstm03a.Stm` (which keep the kernel away from `fitBin`'s unary range test), and the
comparisons of `EquivLean.Demo.Cobol.Cbstm03a.StmCore.Omega` (subscript offsets and bounds).
-/
import EquivLean.Demo.Cobol.Cbstm03a.Stm.WalkSummary
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Omega

namespace Cobol.StmCore

syntax "stm_auto" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| stm_auto) => `(tactic| cobol_auto [stm_flow, Cobol.Stm.execStmt_move_num_num,
      Cobol.StmCore.omegaNatLt, Cobol.StmCore.omegaNatLe, Cobol.StmCore.omegaNatEq,
      Cobol.StmCore.omegaNatBEq, Cobol.StmCore.omegaIntLe, Cobol.StmCore.omegaIntLt])
  | `(tactic| stm_auto [$xs,*]) => `(tactic| cobol_auto [stm_flow, Cobol.Stm.execStmt_move_num_num,
      Cobol.StmCore.omegaNatLt, Cobol.StmCore.omegaNatLe, Cobol.StmCore.omegaNatEq,
      Cobol.StmCore.omegaNatBEq, Cobol.StmCore.omegaIntLe, Cobol.StmCore.omegaIntLt, $xs,*])

end Cobol.StmCore
