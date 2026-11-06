-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW5d.lean (sha256 9edcc4a313f70904...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W5d
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W5d`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

attribute [local irreducible] Top.WsRel Top.TranFields Top.KeepsNonWs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wtr_c8_t (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State)
    (hLC : ∃ fs, σ.heap w = some (.plain "Cbtrn03c$Ws" fs) ∧
      Fields.get fs ("Cbtrn03c$Ws", "lineCounter") = some (.long (BitVec.ofNat 64 (rep1 d s).lc)))
    (hlc : (rep1 d s).lc < 1000000000)
    (hI : Top.WsRel σ w ld lr d (rep1 d s) ∧ wtrK w c ty ca t y cc σ0 fr σ) :
    wtrThinWP w ld lr c ty ca d s t y cc args σ0 8 fr σ := by

  jvc [wtrThinWP, wtrInv, wtrK, StrMono, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, rep2, srem20_ofNat, ofNat64_eq_zero_iff, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
