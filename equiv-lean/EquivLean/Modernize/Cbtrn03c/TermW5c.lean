-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW5c.lean (sha256 df56b2c44d230b79...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W5c
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W5c`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

attribute [local irreducible] Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_f14_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (htamt : (Model.tAmt t).natAbs < 100000000000)
    (hx : (Model.xAcct s.xref).natAbs < 100000000000)
    (hcw : c ≠ w)
    (hTA : ∃ fsT, σ.heap c = some (.plain Top.tranC fsT) ∧
      Top.LFld Top.tranC fsT "tranAmt" (Model.tAmt t))
    (hI : Top.WsRel σ w ld lr d (rep2 (rep1 d s)) ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 14 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, Top.WsRel, Top.StOk, Top.LFld, Top.tranC, Top.wsC, Top.fdC, rep3, rep3_xref, rep2_xref, rep1_xref, add11_ofInt_lit, trunc11_lt, top_recsAt_setObj_ws2, tranFields_setObj_ws2, keepsNonWs_setObj_ws2, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
