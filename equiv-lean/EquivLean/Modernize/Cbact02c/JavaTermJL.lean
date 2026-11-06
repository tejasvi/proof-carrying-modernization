-- Termination package by JimpleLean's session: TermPk/Cbact02c/JavaTermJL.lean (sha256 5d38b2738b19b1b6...); only the module root renamed.
import EquivLean.Modernize.Cbact02c.JavaRun
import EquivLean.Modernize.JL.Cbact02cTermRun

/-!
# CBACT02C → Java: `run` terminates on every input of `runSpec`, and is totally correct

JimpleLean's termination theorem (`EquivLean.Modernize.JL.run_term`, over its contract `runSpecJ`) on
the inputs of our `runSpec`: their record objects satisfy `runSpecJ`'s precondition as in
`sat_runSpec_of_J`. With `sat_runSpec_of_J`, total correctness (`Jimple.total_of_sat_mterm`).
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact02c.Java

open EquivLean.Modernize.JL EquivLean.Modernize.JLBridge

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨a, vals, rfl, ⟨et, xs, hheap, hlen, hrec⟩, hv, hi1, hi2, hi3⟩ := hpre
  have hok : ∀ x ∈ xs, ∃ c, x = .ref c ∧ CardOk σ c := by
    intro x hx
    obtain ⟨v, hvm, hxv⟩ := forall2_mem hrec x hx
    obtain ⟨c, rfl, hc, -⟩ := jrec_card hxv (hv v hvm)
    exact ⟨c, rfl, hc⟩
  exact EquivLean.Modernize.JL.run_term [.ref a] σ ⟨a, et, xs, rfl, hheap, hlen, hok, hi1, hi2, hi3⟩

/-- **CBACT02C → Java, total correctness**: on every input of `runSpec`, `run` has an outcome, and
    every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm (sat_runSpec_of_J EquivLean.Modernize.JL.run_sat) run_term

end EquivLean.Modernize.Cbact02c.Java

#print axioms EquivLean.Modernize.Cbact02c.Java.run_term
#print axioms EquivLean.Modernize.Cbact02c.Java.run_total
