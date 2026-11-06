import EquivLean.Modernize.Cbtrn03c.JavaW.W4

/-!
# CBTRN03C → Java: `writeHeaders`, the entry segment and the first `writeLine` (to the cut at 17)

Each segment unfolds only the cuts it starts from and ends at; the line texts stay folded
where they are not built (their lengths by the `_length` lemmas).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_entry (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State)
    (hpre : args = [.ref w] ∧ WsAt σ0 w ld lr v ∧ v.rsRef = .ref xs ∧
      σ0.heap xs = some (.str rs) ∧ v.reRef = .ref xe ∧ σ0.heap xe = some (.str re) ∧
      rs.length < 1000 ∧ re.length < 1000 ∧ σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done) :
    whWP w ld lr v xs xe rs re args σ0 0 (Frame.init true args) σ0 := by
  jvc [whWP, writeHeadersInv, whI1, nameHeaderJ, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg1 (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI1 w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 14 fr σ := by
  jvc [whWP, writeHeadersInv, whI1, whI2, NewRecT, hdr1V, nameHeaderJ_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_entry
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg1
