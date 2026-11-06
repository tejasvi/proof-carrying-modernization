-- Termination package by JimpleLean's session: TermT4/ZzBTotal.lean (sha256 701b581f9022c5d7...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.ZzP
import EquivLean.Demo.Thrift.Java.Term.ZzBT

/-!
# Thrift → Java (T4): the zigzag methods terminate, and are totally correct

From the partial-correctness VCs (`zz32_body`, `zz64_body`, `uzz32_body`, `uzz64_body`) and their thin
twins (`TermVC.of_thinX`), against the empty contract table (`valid_empty`): no hypothesis, no
premise.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **`intToZigZag(int)` terminates** on every input of its contract. -/
theorem zz32_term {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, zz32Spec.pre args σ → MTerm P zz32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_empty P))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (zz32_body P hF)
      (zz32_thin P hF))

/-- **`intToZigZag(int)`, total correctness.** -/
theorem zz32_total {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, zz32Spec.pre args σ →
      (∃ o, MExec P zz32Ref args σ o) ∧ ∀ o, MExec P zz32Ref args σ o → zz32Spec.post args σ o :=
  fun args σ hpre =>
    ⟨(zz32_term hF args σ hpre).run, fun o ho => BodyVCP.sat zz32_body hF (valid_empty P) args σ o hpre ho⟩

/-- **`longToZigzag(long)` terminates** on every input of its contract. -/
theorem zz64_term {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, zz64Spec.pre args σ → MTerm P zz64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_empty P))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (zz64_body P hF)
      (zz64_thin P hF))

/-- **`longToZigzag(long)`, total correctness.** -/
theorem zz64_total {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, zz64Spec.pre args σ →
      (∃ o, MExec P zz64Ref args σ o) ∧ ∀ o, MExec P zz64Ref args σ o → zz64Spec.post args σ o :=
  fun args σ hpre =>
    ⟨(zz64_term hF args σ hpre).run, fun o ho => BodyVCP.sat zz64_body hF (valid_empty P) args σ o hpre ho⟩

/-- **`zigzagToInt(int)` terminates** on every input of its contract. -/
theorem uzz32_term {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, uzz32Spec.pre args σ → MTerm P uzz32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_empty P))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (uzz32_body P hF)
      (uzz32_thin P hF))

/-- **`zigzagToInt(int)`, total correctness.** -/
theorem uzz32_total {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, uzz32Spec.pre args σ →
      (∃ o, MExec P uzz32Ref args σ o) ∧ ∀ o, MExec P uzz32Ref args σ o → uzz32Spec.post args σ o :=
  fun args σ hpre =>
    ⟨(uzz32_term hF args σ hpre).run,
      fun o ho => BodyVCP.sat uzz32_body hF (valid_empty P) args σ o hpre ho⟩

/-- **`zigzagToLong(long)` terminates** on every input of its contract. -/
theorem uzz64_term {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, uzz64Spec.pre args σ → MTerm P uzz64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_empty P))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (uzz64_body P hF)
      (uzz64_thin P hF))

/-- **`zigzagToLong(long)`, total correctness.** -/
theorem uzz64_total {P : Program} (hF : Contains P [cpC]) :
    ∀ args σ, uzz64Spec.pre args σ →
      (∃ o, MExec P uzz64Ref args σ o) ∧ ∀ o, MExec P uzz64Ref args σ o → uzz64Spec.post args σ o :=
  fun args σ hpre =>
    ⟨(uzz64_term hF args σ hpre).run,
      fun o ho => BodyVCP.sat uzz64_body hF (valid_empty P) args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.zz32_total
#print axioms EquivLean.Demo.Thrift.Java.zz64_total
#print axioms EquivLean.Demo.Thrift.Java.uzz32_total
#print axioms EquivLean.Demo.Thrift.Java.uzz64_total
