-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermRun.lean (sha256 d3b58610a9d22e44...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRun
import EquivLean.Modernize.Cbtrn01c.JavaTermEntry
import EquivLean.Modernize.Cbtrn01c.JavaTermInit
import EquivLean.Modernize.Cbtrn01c.JavaTermCases
import EquivLean.Modernize.Cbtrn01c.JavaTermHelpers

/-!
# CBTRN01C → Java: `run` terminates, and is totally correct

`run_thin` collects the thin VCs of `run` (entry path and cut points 22, 29, 60, 92, as `run_vc`);
with `run_vc` it gives the termination VC (`Jimple.TermVC.of_thin`), and with the callee contracts
(valid, `callees_valid`; terminating, `callees_term`) termination (`Jimple.TermVC.mterm`).
`run_total`: with `run_sat`, every call of `run` on inputs of `runSpec` has an outcome and every
outcome satisfies `runSpec` (`Jimple.total_of_sat_mterm`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

attribute [local irreducible] bodyWP

theorem run_thin (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    ThinVC Gen.prog callees.env 1 runRef (runSpecG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5)
      (runInv a1 a3 a5 vals1 vals3 vals5) runVs 60 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0 hpre
  have hargs : args = runArgs a1 a2 a3 a4 a5 a6 := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have hl : ((runInv a1 a3 a5 vals1 vals3 vals5).inst (runArgs a1 a2 a3 a4 a5 a6) σ0).lookup 0 =
        none := rfl
    have h := run_tseg0 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 hpre
    unfold RunThinWP0 at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · have h := run_tseg22 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hJ
      unfold RunThinWP at h
      exact h
    · have h := run_tseg29 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunThinWP at h
      exact h
    · have h := run_tseg60 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunThinWP at h
      exact h
    · have h := run_tseg92 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunThinWP at h
      exact h

/-- `run` terminates, for the contract with fixed ghost values. -/
theorem run_termG (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    ∀ args σ, (runSpecG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5).pre args σ → MTerm Gen.prog runRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) callees_valid callees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (run_vc a1 a2 a3 a4 a5 a6 vals1 vals3 vals5)
      (run_thin a1 a2 a3 a4 a5 a6 vals1 vals3 vals5))

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨a1, a2, a3, a4, a5, a6, vals1, vals3, vals5, rfl, h1, h3, h5, hv1, hv3, hv5, i1, i2, i3,
    i4, i5, i6, i7, i8⟩ := hpre
  exact run_termG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 _ σ
    ⟨rfl, ⟨h1, h3, h5, hv1, hv3, hv5⟩, ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩⟩

/-- **CBTRN01C → Java, total correctness**: on every input of `runSpec`, `run` has an outcome, and
    every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.Cbtrn01c.Java

#print axioms EquivLean.Modernize.Cbtrn01c.Java.run_term
#print axioms EquivLean.Modernize.Cbtrn01c.Java.run_total
