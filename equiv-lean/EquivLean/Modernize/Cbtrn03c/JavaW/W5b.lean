import EquivLean.Modernize.Cbtrn03c.JavaW.W5

/-!
# CBTRN03C → Java: `writeTransactionReport`, the segments that call (from the cuts at 7, 12, 13, 22)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem wsRel_congr {σ : State} {w ld lr : Addr} {d : List EquivLean.Cobol.Rec.FVal}
    {s s' : Model.St} (h : Top.WsRel σ w ld lr d s) (e : s = s') : Top.WsRel σ w ld lr d s' :=
  e ▸ h

attribute [local irreducible] Top.WsRel Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s7 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hd : WsDateparmRecord.Valid d)
    (hI : Top.WsRel σ w ld lr d (rep0 d s) ∧ (rep0 d s).first = false ∧ s.first = true ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrWP w ld lr c ty ca d s t y cc args σ0 7 fr σ := by
  jvc [wtrWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeHeadersSpecM, rep1]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s12 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : Top.WsRel σ w ld lr d (rep1 d s) ∧ (rep1 d s).lc % 20 = 0 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrWP w ld lr c ty ca d s t y cc args σ0 12 fr σ := by
  jvc [wtrWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, Top.writePageTotalsSpecM, Top.wsStepSpec, pageTotals_first, rep1_first]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s13 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hd : WsDateparmRecord.Valid d)
    (hI : Top.WsRel σ w ld lr d (Model.pageTotals (rep1 d s)) ∧
      (Model.pageTotals (rep1 d s)).first = false ∧ (rep1 d s).lc % 20 = 0 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrWP w ld lr c ty ca d s t y cc args σ0 13 fr σ := by
  jvc [wtrWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeHeadersSpecM, rep2]
  all_goals
    refine wsRel_congr (by assumption) ?_
    simp only [Model.pageTotals, Model.inc, Model.wr, Model.St.mk.injEq, List.append_assoc,
      List.cons_append, List.nil_append, true_and, and_true]
    all_goals omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_s22 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hI : Top.WsRel σ w ld lr d (rep3 (rep2 (rep1 d s)) t) ∧
      (Model.xAcct (rep3 (rep2 (rep1 d s)) t).xref).natAbs < 100000000000 ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrWP w ld lr c ty ca d s t y cc args σ0 22 fr σ := by
  jvc [wtrWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, reportCalleesR, writeHeadersSig, Top.writePageTotalsSig, writeDetailSig, add11Sig, Carries, writeDetailSpecM, wtrSpecG, report_eq]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wtr_s7
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wtr_s12
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wtr_s13
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wtr_s22
