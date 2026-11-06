import EquivLean.Modernize.Cbtrn03c.JavaW.W5

/-!
# CBTRN03C → Java: `writeTransactionReport`, the segment that reads the line counter
(from the cut at 8 to the cuts at 12 and 14)

`WsRel` stays folded: the counter's field comes as a separate fact (`lc_of_wsRel`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem lc_of_wsRel {σ : State} {w ld lr : Addr} {d : List EquivLean.Cobol.Rec.FVal}
    {s : Model.St} (h : Top.WsRel σ w ld lr d s) :
    (∃ fs, σ.heap w = some (.plain "Cbtrn03c$Ws" fs) ∧
      Fields.get fs ("Cbtrn03c$Ws", "lineCounter") = some (.long (BitVec.ofNat 64 s.lc))) ∧
    s.lc < 1000000000 := by
  obtain ⟨fs, _, _, _, _, _, _, _, hw, -, -, -, -, -, -, -, hl, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, ⟨hlc, -⟩⟩ := h
  exact ⟨⟨fs, hw, hl⟩, hlc⟩

attribute [local irreducible] Top.WsRel Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_c8 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State)
    (hLC : ∃ fs, σ.heap w = some (.plain "Cbtrn03c$Ws" fs) ∧
      Fields.get fs ("Cbtrn03c$Ws", "lineCounter") = some (.long (BitVec.ofNat 64 (rep1 d s).lc)))
    (hlc : (rep1 d s).lc < 1000000000)
    (hI : Top.WsRel σ w ld lr d (rep1 d s) ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrWP w ld lr c ty ca d s t y cc args σ0 8 fr σ := by
  jvc [wtrWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, rep2, srem20_ofNat, ofNat64_eq_zero_iff]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wtr_c8
