-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW3b.lean (sha256 4e317f04c0241566...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W3b
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W3b`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wat_seg1_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) (hI : watI1 w ld lr v σ0 fr σ) : watThinWP w ld lr v args σ0 11 fr σ := by

  jvc [watThinWP, writeAccountTotalsSpecG, writeAccountTotalsInv, watI1, watI2, acct1V, acct2V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wat_seg2_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) (hI : watI2 w ld lr v σ0 fr σ) : watThinWP w ld lr v args σ0 15 fr σ := by

  jvc [watThinWP, writeAccountTotalsSpecG, writeAccountTotalsInv, watI1, watI2, acct1V, acct2V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wgt_seg1_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) (hI : wgtI1 w ld lr v σ0 fr σ) : wgtThinWP w ld lr v args σ0 11 fr σ := by

  jvc [wgtThinWP, writeGrandTotalsSpecG, writeGrandTotalsInv, wgtI1, grand1V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
