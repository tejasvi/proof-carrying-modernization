import EquivLean.Modernize.Cbtrn03c.JavaW.W4

/-!
# CBTRN03C → Java: `writeHeaders`, the segments from the cuts at 17, 35, 38

Each segment unfolds only the cuts it starts from and ends at; the line texts stay folded
where they are not built (their lengths by the `_length` lemmas).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg2 (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI2 w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 17 fr σ := by
  jvc [whWP, writeHeadersInv, whI2, whI2a, NewRecT, hdr1V, hdr2V, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg2a (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI2a w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 25 fr σ := by
  jvc [whWP, writeHeadersInv, whI2a, whI2b, NewRecT, hdr2V, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg2b (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI2b w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 29 fr σ := by
  jvc [whWP, writeHeadersInv, whI2b, whI3, NewRecT, hdr2V, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg3 (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI3 w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 35 fr σ := by
  jvc [whWP, writeHeadersInv, whI3, whI4, NewRecT, hdr2V, hdr3V, header1J_length, dashJ, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wh_seg4 (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (fr : Frame) (σ : State)
    (hI : whI4 w ld lr v rs re σ0 fr σ) :
    whWP w ld lr v xs xe rs re args σ0 38 fr σ := by
  jvc [whWP, writeHeadersInv, writeHeadersSpecG, whI4, NewRecT, RecT, hdr3V, hdr4V, dashJ_length, linesCallees, padSig, spacesSig, repeatSig, digitsSig, editSig, writeLineSig, incLineSig, WsAt, Frame3, Grows, wsC, fdC, incL, setWidth_45, setWidth_32, argText, strOf, wsF, wsFs, refOf, longOf, listVals, listMods, lrOf, fixJ_length, repJ_length, spJ_length, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, valueOfArg_char, JType.isRef, exists_eq_left', exists_and_left, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg2
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg2a
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg2b
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg3
#print axioms EquivLean.Modernize.Cbtrn03c.Java.wh_seg4
