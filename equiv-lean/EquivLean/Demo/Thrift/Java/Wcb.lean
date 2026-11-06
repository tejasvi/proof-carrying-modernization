import EquivLean.Demo.Thrift.Java.WcbD

/-!
# Thrift → Java (T4): `writeCollectionBegin(elemType, size)`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wcb_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    MethodVC P (Γ5 P R) 2 wcbRef (wcbSpecI P R) [] 200 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, wcbSpecI, Γ5, Γ2, wbdSig, rv32Sig, wv32Sig, wbdN,
    Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer,
    tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame,
    ttCls, cpCls, tpCls]
  case isTrue.right.normal.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case isTrue.right.normal.right.normal =>
    exact wcb_post_long ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case isFalse.right.normal =>
    exact wcb_post_short ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
