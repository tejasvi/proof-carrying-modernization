import EquivLean.Demo.Thrift.Java.RfiC

/-!
# Thrift → Java (T4): `readFieldId(byte)`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rfi_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun P => Γ2 P R) 3 rfiRef (fun P => rfiSpecI P R) [] 200 := by
  jverify_body [Contains, CPAt, ClassOK, rfiSpecI, LastAt, BoolAt, Γ2, rv32Sig, wv32Sig, Program.selectVirtual,
    tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
    tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, ttCls, cpCls, tpCls, tpeCls]
  case isTrue.right.normal.isTrue => exact rfi_g12 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case isTrue.right.normal.isFalse.isTrue =>
    exact rfi_g12 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case isTrue.right.normal.isFalse.isFalse =>
    exact rfi_g3 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case isTrue.right.exc.some => exact rfi_g4 ‹_› ‹_› ‹_› ‹_› ‹_›
  case isFalse.isTrue => exact rfi_g56 ‹_› ‹_› ‹_› ‹_›
  case isFalse.isFalse.isTrue => exact rfi_g56 ‹_› ‹_› ‹_› ‹_›
  case isFalse.isFalse.isFalse => exact rfi_g7 ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
