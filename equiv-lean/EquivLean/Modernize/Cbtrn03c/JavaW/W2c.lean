import EquivLean.Modernize.Cbtrn03c.JavaW.W2

/-!
# CBTRN03C → Java: `writePageTotals`, the second `writeLine` (statements 19–21)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wpt_seg2 (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) (hI : wptI2 w ld lr v σ0 fr σ) : wptWP w ld lr v args σ0 19 fr σ := by
  jvc [wptWP, writePageTotalsSpecG, writePageTotalsInv, wptI1, wptI2, totalsCallees, padSig,
    repeatSig, editSig, add11Sig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC,
    page1V, page2V, totalLineJ, dashJ, add11J, incL, argText, strOf, wsF, wsFs, refOf, longOf,
    listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg,
    Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wpt_seg2
