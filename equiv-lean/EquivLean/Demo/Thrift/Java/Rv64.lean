import EquivLean.Demo.Thrift.Java.Rv64C

/-!
# Thrift → Java (T4): `TCompactProtocol.readVarint64()` reads the varint (D, M)

The buffer fast path (at least 5 bytes in the buffer: the groups are read from `getBuffer()`, then
`consumeBuffer(n)`) or byte by byte with `readByte()`. At most 5 bytes: a fifth byte with the high
bit set throws a `TProtocolException`; the value is the groups ORed into an `int` (a fifth group
above bit 31 is lost, `v mod 2^32`); an input that ends inside the varint throws the transport's
`TTransportException`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rv64_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (fun _ => (tContracts R).env) 3 rv64Ref (fun P => rv64SpecI P R) (rv64Inv R) 200 := by
  jverify_body [Contains, CPAt, CPAtR, ClassOK, rv64SpecI, rv64Inv, PFrame, Program.selectVirtual,
    tc_write, tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition,
    tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, BufView, TFrame, List.getElem?_eq_getElem,
    List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem_cons_zero,
    getElem?_zero_of_one32, jbyte, instanceFields_tpe, ctorCall_exc_str, ttCls, cpCls, tpCls, tpeCls]
  case left.some.true.normal.isTrue => exact rv64_g1 ‹_›
  case left.some.true.normal.isFalse.right.normal.right.normal =>
    exact rv64_g2 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.left.isTrue.isTrue.isTrue => exact rv64_g3 ‹_› ‹_› ‹_› ‹_›
  case right.left.isTrue.isTrue.isFalse =>
    exact rv64_g4 ‹_› ‹_› ‹_› ‹_› ‹_› (heap_newExc _ _ _ _ _ _)
  case right.left.isTrue.isFalse.some.true.left => exact rv64_g5 ‹_› ‹_› ‹_›
  case right.left.isTrue.isFalse.some.true.right.normal =>
    exact rv64_g6 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isTrue => exact rv64_g7 ‹_› ‹_› ‹_› ‹_› (heap_newExc _ _ _ _ _ _)
  case right.right.isFalse.some.true.normal.isTrue.left => exact rb_readAll_pre R ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isFalse.some.true.normal.isTrue.right.normal.isTrue =>
    exact rv64_g9 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isFalse.some.true.normal.isTrue.right.normal.isFalse =>
    exact rv64_g10 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isFalse.some.true.normal.isTrue.right.exc => exact rv64_g11 ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isFalse.some.true.normal.isFalse.right.normal.right.normal.right.normal.isTrue =>
    exact rv64_g12 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.isFalse.some.true.normal.isFalse.right.normal.right.normal.right.normal.isFalse =>
    exact rv64_g13 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
