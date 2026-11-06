import EquivLean.Demo.Thrift.Java.RlbD

/-!
# Thrift → Java (T4): `checkContainerReadLength(int)`, its body
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ccrl_body : BodyVCP (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) 3 ccrlRef
    (fun _ => ccrlSpec) [] 100 := by
  jverify_body [Contains, ccrlSpec, instanceFields_tpe, ctorCall_exc_str, instanceFields_sb, ctorCall_sb,
    tpeCls, cpCls]
  case isTrue.isTrue.isFalse.isTrue => exact ccrl_ok ‹_› ‹_› ‹_› (inLimit_toLong _)
  case isTrue.isTrue.isFalse.isFalse =>
    refine ccrl_exc ‹_› ‹_› (Or.inr (notIn_1 ‹_› ‹_› ‹_›)) ?_
    simp only [State.next_setObj, State.next_alloc]
    exact lt_add4 _
  case isTrue.isFalse.isTrue => exact ccrl_ok ‹_› ‹_› ‹_› (inLimit_m1 _)
  case isTrue.isFalse.isFalse.isTrue => exact ccrl_ok ‹_› ‹_› ‹_› (inLimit_lt ‹_›)
  case isTrue.isFalse.isFalse.isFalse.isTrue => exact ccrl_ok ‹_› ‹_› ‹_› (inLimit_toLong _)
  case isTrue.isFalse.isFalse.isFalse.isFalse =>
    refine ccrl_exc ‹_› ‹_› (Or.inr (notIn_2 ‹_› ‹_› ‹_›)) ?_
    simp only [State.next_setObj, State.next_alloc]
    exact lt_add4 _
  case isFalse =>
    refine ccrl_exc ‹_› ‹_› (Or.inl (by omega)) ?_
    simp only [State.next_setObj, State.next_alloc]
    exact lt_add4 _

end EquivLean.Demo.Thrift.Java
