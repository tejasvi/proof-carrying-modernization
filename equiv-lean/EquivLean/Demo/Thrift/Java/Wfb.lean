import EquivLean.Demo.Thrift.Java.WfbC

/-!
# Thrift → Java (T4): `writeFieldBeginInternal(field, typeOverride)`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wfb_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    MethodVC P (Γ4 P R) 2 wfbRef (wfbSpecI P R) (wfbInv P R) 200 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, wfbSpecI, wfbInv, FieldIdAt, LastAt, Γ4, Γ2, wbdSig, wi16Sig, gctSig,
    rv32Sig, wv32Sig, gctSpec, wbdN, wi16N, Program.selectVirtual, tc_write, tc_readAll,
    tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, ttCls, cpCls, tpCls, tfCls]
  case left.isTrue.none => exact (wfb_neg1 ‹_›).elim
  case left.isTrue.some => exact (wfb_neg1 ‹_›).elim
  case left.isFalse.isTrue.right.normal.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case left.isFalse.isTrue.right.normal.right.normal.right.left =>
    exact wfb_heap_f ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.isFalse.isTrue.right.normal.right.normal.right.right.right.left =>
    exact wfb_bytes_le ‹_›
  case left.isFalse.isTrue.right.normal.right.normal.right.right.right.right.right.right =>
    exact wfb_heap_a ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.isFalse.isFalse.isTrue.right.normal.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case left.isFalse.isFalse.isTrue.right.normal.right.normal.right.left =>
    exact wfb_heap_f ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.isFalse.isFalse.isTrue.right.normal.right.normal.right.right.right.left =>
    exact wfb_bytes_gt ‹_› ‹_›
  case left.isFalse.isFalse.isTrue.right.normal.right.normal.right.right.right.right.right.right =>
    exact wfb_heap_a ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.isFalse.isFalse.isFalse.right.normal.right.right.right.left =>
    exact wfb_bytes_short ‹_› ‹_› ‹_›
  case right => exact wfb_exit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
