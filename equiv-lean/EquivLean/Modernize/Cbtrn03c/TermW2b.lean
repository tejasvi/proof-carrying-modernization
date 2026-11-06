-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW2b.lean (sha256 ac23743709b59a73...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W2b
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W2b`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wpt_seg1_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) (hI : wptI1 w ld lr v σ0 fr σ) : wptThinWP w ld lr v args σ0 11 fr σ := by

  jvc [wptThinWP, writePageTotalsSpecG, writePageTotalsInv, wptI1, wptI2, totalsCallees, padSig,
    repeatSig, editSig, add11Sig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC,
    page1V, totalLineJ, dashJ, add11J, incL, setWidth_45, argText, strOf, wsF, wsFs, refOf,
    longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg,
    Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
