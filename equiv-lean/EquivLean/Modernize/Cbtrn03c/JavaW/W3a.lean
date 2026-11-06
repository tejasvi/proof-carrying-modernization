import EquivLean.Modernize.Cbtrn03c.JavaW.W3

/-!
# CBTRN03C → Java: `writeAccountTotals`, `writeGrandTotals`: the entry segments (to the cut at 11)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wat_entry (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writeAccountTotalsSpecG w ld lr v).pre args σ0) :
    watWP w ld lr v args σ0 0 (Frame.init true args) σ0 := by
  jvc [watWP, writeAccountTotalsSpecG, writeAccountTotalsInv, watI1, watI2, acct1V, acct2V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wgt_entry (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State)
    (hpre : (writeGrandTotalsSpecG w ld lr v).pre args σ0) :
    wgtWP w ld lr v args σ0 0 (Frame.init true args) σ0 := by
  jvc [wgtWP, writeGrandTotalsSpecG, writeGrandTotalsInv, wgtI1, grand1V,
    totalsCallees, padSig, repeatSig, editSig, add11Sig, writeLineSig, incLineSig,
    WsAt, Frame3, Grows, wsC, fdC, totalLineJ, dashJ, add11J, incL, setWidth_46, setWidth_45, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, editJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wat_entry
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wgt_entry
