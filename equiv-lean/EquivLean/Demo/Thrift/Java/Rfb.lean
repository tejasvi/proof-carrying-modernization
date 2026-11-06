import EquivLean.Demo.Thrift.Java.RfbC

/-!
# Thrift → Java (T4): `readFieldBegin()`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rfb_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    MethodVC P (Γ3 P R) 3 rfbRef (rfbSpecI P R) (rfbInv P R) 200 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, rfbSpecI, rfbInv, LastAt, BoolAt, Γ3, Γ2, rbSig, gttSig, rfiSig,
    rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame,
    PFrame, RFrame, gttN, gttE, instanceFields_tf, jbyte, tfNew, ttCls, cpCls, tpCls, tpeCls, tfCls]
  case left.right.normal.isTrue => exact rfb_g1 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.right.normal.isFalse.left => exact rfb_g2 _ ‹_› ‹_› ‹_›
  case left.right.normal.isFalse.right.normal => exact rfb_g3 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.right.normal.isFalse.right.exc => exact rfb_g4 ‹_› ‹_› ‹_› ‹_›
  case left.right.exc => exact rfb_g5 ‹_› ‹_› ‹_›
  case right.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case right.right.normal =>
    exact rfb_g7 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (by exact tf_get_type _ _ _ _) (by exact tf_get_id _ _ _ _)
  case right.right.exc.some => exact rfb_g8 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
