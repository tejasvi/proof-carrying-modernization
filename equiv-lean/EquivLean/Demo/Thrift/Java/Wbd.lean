import EquivLean.Demo.Thrift.Java.WfbC

/-!
# Thrift → Java (T4): `writeByteDirect(byte)`: `temp[0] = b; trans_.write(temp, 0, 1)`
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wbd_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    wbdRef (fun P => wbdSpecI P R) [] 60 := by
  jverify_body [Contains, CPAt, ClassOK, wbdSpecI, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none,
    ttCls, cpCls, tpCls]
  case isFalse.some.true.left => exact wbd_pre R ‹_› ‹_› ‹_› ‹_›
  case isFalse.some.true.right.normal =>
    rename_i hw
    exact wbd_post ‹_› ‹_› ‹_›
      (by
        obtain ⟨-, h1, h2, h3, h4⟩ := hw _ _ _ _ _ rfl rfl rfl rfl (by rw [if_pos rfl])
        exact ⟨h1, h2, h3, h4⟩)

end EquivLean.Demo.Thrift.Java
