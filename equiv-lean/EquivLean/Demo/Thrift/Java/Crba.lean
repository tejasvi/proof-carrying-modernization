import EquivLean.Demo.Thrift.Java.RlbD

/-!
# Thrift → Java (T4): `TProtocol.checkReadBytesAvailable(TList)`, its body (on a `TCompactProtocol`)
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem crba_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (fun _ => (tContracts R).env) 4 crbaRef (fun P => crbaSpecI P R) [] 100 := by
  jverify_body [Contains, CPAt, ClassOK, crbaSpecI, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none,
    Program.selectVirtual, instanceFields_tte, ctorCall_exc_str, ttCls, cpCls, tpCls, tlCls, ttExcCls]
  all_goals first
    | (apply crba_ok <;> first | assumption | rfl)
    | (apply crba_exc <;> first
        | assumption
        | (apply minSize_none_k <;> first | assumption | decide)
        | (apply minSize_none_neg; assumption)
        | (apply minSize_none_big; assumption)
        | (simp only [State.next_setObj, State.next_alloc]; exact lt_add2 _))

end EquivLean.Demo.Thrift.Java
