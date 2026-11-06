-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW3a.lean (sha256 69a6a60d3cc41617...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W3a
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W3a`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wat_entry_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writeAccountTotalsSpecG w ld lr v).pre args σ0) :
    watThinWP0 w ld lr v args σ0 := by

  jvc [watThinWP0, writeAccountTotalsSpecG, writeAccountTotalsInv, watI1, watI2, acct1V, acct2V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wgt_entry_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writeGrandTotalsSpecG w ld lr v).pre args σ0) :
    wgtThinWP0 w ld lr v args σ0 := by

  jvc [wgtThinWP0, writeGrandTotalsSpecG, writeGrandTotalsInv, wgtI1, grand1V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
