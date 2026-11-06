import EquivLean.Demo.Thrift.Java.RsbD

/-!
# Thrift → Java (T4): `readSetBegin()`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rsb_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] →
    MethodVC P (Γ7 P R) 3 rsbRef (rsbSpecI P R) (rsbInv P R) 100 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, rsbSpecI, rsbInv, LimitAt, Γ7, rlbSig, Program.selectVirtual, tc_write, tc_readAll,
    tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, instanceFields_ts, tsNew, cpCls, tpCls, tlCls, tsCls]
  case left.right.left => exact alloc_cpAtH _ ‹_›
  case left.right.right.left => exact alloc_src _ ‹_›
  case left.right.right.right.left => exact alloc_sink _ ‹_›
  case left.right.right.right.right.right.right.right => exact alloc_notown _ ‹_›
  case right.left.left => exact rsb_rlb_pre ‹_› ‹_› ‹_›
  case right.left.right.normal =>
    exact rsb_cut3 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.left.right.exc.none => exact (rsb_exc_none ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).elim
  case right.left.right.exc.some => exact rlbE_shift ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right =>
    exact rsb_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (ts_get_elemType _ _ _) (ts_get_size _ _ _)

end EquivLean.Demo.Thrift.Java
