import EquivLean.Demo.Thrift.Java.WfbC

/-!
# Thrift → Java (T4): `writeI16(short)`: `writeVarint32(intToZigZag(i))`
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi16_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun P => Γ2 P R) 1 wi16Ref (fun P => wi16SpecI P R) [] 60 := by
  jverify_body [Contains, CPAt, ClassOK, wi16SpecI, Γ2, rv32Sig, wv32Sig, Program.selectVirtual,
    tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
    tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, ttCls, cpCls, tpCls]
  case right.normal => exact wi16_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
