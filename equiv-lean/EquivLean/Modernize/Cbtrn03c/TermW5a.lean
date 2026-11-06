-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW5a.lean (sha256 fa5c389a73c51b44...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W5a
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W5a`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

attribute [local irreducible] Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_entry_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : args = [.ref w, .ref c, .ref ty, .ref ca] ∧ Top.WsRel σ0 w ld lr d s ∧
      Top.TranFields σ0 c t ∧ σ0.heap ty = some (.str (cp037Str (Model.yDesc y))) ∧
      σ0.heap ca = some (.str (cp037Str (Model.cDesc cc))) ∧
      σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done) :
    wtrThinWP0 w ld lr c ty ca d s t y cc args σ0 := by

  jvc [wtrThinWP0, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, Top.WsRel, Top.StOk, Top.wsC, Top.fdC, rep0, rep1, top_recsAt_setObj_ws, tranFields_setObj_ws, keepsNonWs_setObj_ws0, keepsNonWs_refl, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
