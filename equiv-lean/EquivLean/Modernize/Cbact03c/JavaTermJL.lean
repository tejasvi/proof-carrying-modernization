-- Termination package by JimpleLean's session: TermPk/Cbact03c/JavaTermJL.lean (sha256 8d423ecb78c9fe96...); only the module root renamed.
import EquivLean.Modernize.Cbact03c.JavaRun
import EquivLean.Modernize.JL.Cbact03cTermRun

/-!
# CBACT03C → Java: `run` terminates on every input of `runSpec`, and is totally correct

JimpleLean's termination theorem (`EquivLean.Modernize.JL.c3_run_term`, over its contract
`c3RunSpecJ`) on the inputs of our `runSpec`: their record objects satisfy `c3RunSpecJ`'s precondition
as in `sat_runSpec_of_J`. With `sat_runSpec_of_J`, total correctness (`Jimple.total_of_sat_mterm`).
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact03c.Java

open EquivLean.Modernize.JL EquivLean.Modernize.JLBridge

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨a, vals, rfl, ⟨et, xs, hheap, hlen, hrec⟩, hv, hi1, hi2, hi3, hi4⟩ := hpre
  have hok : ∀ x ∈ xs, ∃ c, x = .ref c ∧ XrefOk σ c := by
    intro x hx
    obtain ⟨v, hvm, hxv⟩ := forall2_mem hrec x hx
    obtain ⟨c, rfl, hc, -⟩ := jrec_xref hxv (hv v hvm)
    exact ⟨c, rfl, hc⟩
  exact EquivLean.Modernize.JL.c3_run_term [.ref a] σ
    ⟨a, et, xs, rfl, hheap, hlen, hok, hi1, hi2, hi3, hi4⟩

/-- **CBACT03C → Java, total correctness**: on every input of `runSpec`, `run` has an outcome, and
    every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm (sat_runSpec_of_J EquivLean.Modernize.JL.c3_run_sat) run_term

end EquivLean.Modernize.Cbact03c.Java

#print axioms EquivLean.Modernize.Cbact03c.Java.run_term
#print axioms EquivLean.Modernize.Cbact03c.Java.run_total
