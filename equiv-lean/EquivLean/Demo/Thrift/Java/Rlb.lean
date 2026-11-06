import EquivLean.Demo.Thrift.Java.RlbC

/-!
# Thrift → Java (T4): `readListBegin()`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rlb_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC] →
    MethodVC P (Γ6 P R) 2 rlbRef (rlbSpecI P R) (rlbInv P R) 300 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, rlbSpecI, rlbInv, LimitAt, Γ6, Γ2, rbSig, gttSig, ccrlSig, crbaSig,
    rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame,
    PFrame, gttN, gttE, ccrlN, ccrlE, crbaN, crbaE, instanceFields_tl, jbyte,
    tlNew, ttCls, cpCls, tpCls, tpeCls, tlCls]
  case left.right.normal.left => exact rlb_nib ‹_› ‹_›
  case left.right.exc => exact rlb_rb_exc ‹_› ‹_› ‹_›
  case right.left.isTrue.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case right.left.isTrue.right.normal =>
    exact rlb_cut7_long ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.left.isTrue.right.exc.some => exact rlb_rv32_exc ‹_› ‹_› ‹_› ‹_›
  case right.left.isFalse => exact rlb_cut7_short ‹_› ‹_› ‹_›
  case right.right.normal.left => exact rlb_gtt_pre _ ‹_›
  case right.right.normal.right.normal.left =>
    exact rlb_crba_pre ‹_› (tl_get_elemType _ _ _) (tl_get_size _ _ _)
  case right.right.normal.right.normal.right.normal =>
    exact rlb_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (tl_get_elemType _ _ _) (tl_get_size _ _ _) ‹_›
  case right.right.normal.right.normal.right.exc =>
    exact rlb_crba_exc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.normal.right.exc => exact rlb_gtt_exc ‹_› ‹_›
  case right.right.exc => exact rlb_ccrl_exc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
