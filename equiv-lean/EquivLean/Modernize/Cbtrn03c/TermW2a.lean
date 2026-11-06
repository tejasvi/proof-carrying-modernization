-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermW2a.lean (sha256 9ebbbd2f7329dcce...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W2a
import EquivLean.Modernize.Cbtrn03c.JavaTermWDefs

/-!
# Termination: thin twins of `W2a`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wpt_entry_t (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writePageTotalsSpecG w ld lr v).pre args σ0) :
    wptThinWP0 w ld lr v args σ0 := by

  jvc [wptThinWP0, writePageTotalsSpecG, writePageTotalsInv, wptI1, wptI2, totalsCallees, padSig,
    repeatSig, editSig, add11Sig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, totalLineJ,
    setWidth_46, argText, strOf, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref,
    JType.isRef, exists_eq_left', exists_and_left, and_assoc, wLineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java
