-- Termination package by JimpleLean's session: TermT4/CcrlTotal.lean (sha256 13d07fcb2d20521c...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.RlbP
import EquivLean.Demo.Thrift.Java.Term.CcrlT

/-!
# Thrift → Java (T4): `checkContainerReadLength(int)` terminates, and is totally correct

From the partial-correctness VC (`ccrl_body`) and its thin twin (`TermVC.of_thinX`), against the empty
contract table: no hypothesis, no premise.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **`checkContainerReadLength(int)` terminates** on every input of its contract. -/
theorem ccrl_term {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, ccrlSpec.pre args σ → MTerm P ccrlRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Valid.strengthen noX (fun _ _ h => by simp [Contracts.env, List.lookup] at h))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (ccrl_body P hF)
      (ccrl_thin P hF))

/-- **`checkContainerReadLength(int)`, total correctness.** -/
theorem ccrl_total {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, ccrlSpec.pre args σ →
      (∃ o, MExec P ccrlRef args σ o) ∧ ∀ o, MExec P ccrlRef args σ o → ccrlSpec.post args σ o :=
  fun args σ hpre => ⟨(ccrl_term hF args σ hpre).run, fun o ho => ccrl_sat hF args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.ccrl_total
