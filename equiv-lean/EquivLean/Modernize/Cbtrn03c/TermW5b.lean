-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW5b.lean (sha256 1e226f252c255505...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W5b
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W5b`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

attribute [local irreducible] Top.WsRel Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s7_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hd : WsDateparmRecord.Valid d)
    (hI : Top.WsRel σ w ld lr d (rep0 d s) ∧ (rep0 d s).first = false ∧ s.first = true ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 7 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeHeadersSpecM, rep1, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s12_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : Top.WsRel σ w ld lr d (rep1 d s) ∧ (rep1 d s).lc % 20 = 0 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 12 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, Top.writePageTotalsSpecM, Top.wsStepSpec, pageTotals_first, rep1_first, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s13_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hd : WsDateparmRecord.Valid d)
    (hI : Top.WsRel σ w ld lr d (Model.pageTotals (rep1 d s)) ∧
      (Model.pageTotals (rep1 d s)).first = false ∧ (rep1 d s).lc % 20 = 0 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 13 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeHeadersSpecM, rep2, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s22_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hI : Top.WsRel σ w ld lr d (rep3 (rep2 (rep1 d s)) t) ∧
      (Model.xAcct (rep3 (rep2 (rep1 d s)) t).xref).natAbs < 100000000000 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 22 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeDetailSpecM, wtrSpecG, report_eq, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
