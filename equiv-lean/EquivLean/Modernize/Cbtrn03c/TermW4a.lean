-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW4a.lean (sha256 fee1014991a73a44...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W4a
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W4a`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_entry_t (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State)
    (hpre : args = [.ref w] ∧ WsAt σ0 w ld lr v ∧ v.rsRef = .ref xs ∧
      σ0.heap xs = some (.str rs) ∧ v.reRef = .ref xe ∧ σ0.heap xe = some (.str re) ∧
      rs.length < 1000 ∧ re.length < 1000 ∧ σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done) :
    whThinWP0 w ld lr v xs xe rs re args σ0 := by

  jvc [whThinWP0, writeHeadersInv, whI1, nameHeaderJ, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg1_t (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI1 w ld lr v rs re σ0 fr σ) :
    whThinWP w ld lr v xs xe rs re args σ0 14 fr σ := by

  jvc [whThinWP, writeHeadersInv, whI1, whI2, NewRecT, hdr1V, nameHeaderJ_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
