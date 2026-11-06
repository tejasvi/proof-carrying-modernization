import EquivLean.Modernize.Cbtrn03c.JavaW.W4

/-!
# CBTRN03C → Java: `writeDetail`, its segments (cuts at 18, 28, 37)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wd_entry (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State)
    (hpre : args = [.ref w, .ref c, .ref yx, .ref cx] ∧ WsAt σ0 w ld lr v ∧
      -9223372036854775808 < v.acctId.toInt ∧ DetailFields σ0 c t ∧
      (Model.tId t).length < 1000 ∧ (Model.tType t).length < 1000 ∧
      (Model.tSource t).length < 1000 ∧
      -9223372036854775808 < (BitVec.ofInt 64 (Model.tCat t)).toInt ∧
      -9223372036854775808 < (BitVec.ofInt 64 (Model.tAmt t)).toInt ∧
      σ0.heap yx = some (.str ys) ∧ ys.length < 1000 ∧ σ0.heap cx = some (.str cs) ∧
      cs.length < 1000 ∧ σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done) :
    wdWP w ld lr v c yx cx t ys cs args σ0 0 (Frame.init true args) σ0 := by
  jvc [wdWP, writeDetailInv, wdA, detP1, DetailFields, Top.SFld, Top.LFld, Top.tranC, editJ_length, zpadJ_length', cp037Str_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wd_segA (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : wdA w ld lr v c yx cx t ys cs σ0 fr σ) :
    wdWP w ld lr v c yx cx t ys cs args σ0 18 fr σ := by
  jvc [wdWP, writeDetailInv, wdA, wdB, detP2, DetailFields, Top.SFld, Top.LFld, Top.tranC, editJ_length, zpadJ_length', cp037Str_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wd_segB (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : wdB w ld lr v c t ys cs σ0 fr σ) :
    wdWP w ld lr v c yx cx t ys cs args σ0 28 fr σ := by
  jvc [wdWP, writeDetailInv, wdB, wdI1, detailJ, DetailFields, Top.SFld, Top.LFld, Top.tranC, editJ_length, zpadJ_length', cp037Str_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wd_seg1 (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : wdI1 w ld lr v t ys cs σ0 fr σ) :
    wdWP w ld lr v c yx cx t ys cs args σ0 37 fr σ := by
  jvc [wdWP, writeDetailInv, writeDetailSpecG, wdI1, det1V, RecT, detailJ_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wd_entry
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wd_segA
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wd_segB
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wd_seg1
