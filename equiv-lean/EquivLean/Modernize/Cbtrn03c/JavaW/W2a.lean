import EquivLean.Modernize.Cbtrn03c.JavaW.W2

/-!
# CBTRN03C → Java: `writePageTotals`, entry segment (statements 0–10, to the cut at 11)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wpt_entry (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writePageTotalsSpecG w ld lr v).pre args σ0) :
    wptWP w ld lr v args σ0 0 (Frame.init true args) σ0 := by
  jvc [wptWP, writePageTotalsSpecG, writePageTotalsInv, wptI1, wptI2, totalsCallees, padSig,
    repeatSig, editSig, add11Sig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, totalLineJ,
    setWidth_46, argText, strOf, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref,
    JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wpt_entry
