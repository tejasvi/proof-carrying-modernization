-- Termination package by JimpleLean's session: TermT4/GttTotal.lean (sha256 4fe557d78798ab96...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.FhR
import EquivLean.Demo.Thrift.Java.Term.GttT

/-!
# Thrift → Java (T4): `getTType(byte)` terminates, and is totally correct

From the partial-correctness VC (`gtt_body`) and its thin twin (`TermVC.of_thinX`), against the empty
contract table: no hypothesis, no premise.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **`getTType(byte)` terminates** on every input of its contract. -/
theorem gtt_term {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, gttSpec.pre args σ → MTerm P gttRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Valid.strengthen noX (fun _ _ h => by simp [Contracts.env, List.lookup] at h))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (gtt_body P hF)
      (gtt_thin P hF))

/-- **`getTType(byte)`, total correctness.** -/
theorem gtt_total {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, gttSpec.pre args σ →
      (∃ o, MExec P gttRef args σ o) ∧ ∀ o, MExec P gttRef args σ o → gttSpec.post args σ o :=
  fun args σ hpre => ⟨(gtt_term hF args σ hpre).run, fun o ho => gtt_sat hF args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.gtt_total
