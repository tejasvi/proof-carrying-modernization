-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermRun.lean (sha256 d9bede479a317b6a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.JavaTermHelpLink
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg0X
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg12X
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg22X
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg35X
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg44X
import EquivLean.Modernize.Cbtrn02c.JavaTermSeg48X
import EquivLean.Modernize.Cbtrn02c.JavaTermRunL65c
import EquivLean.Modernize.Cbtrn02c.JavaTermRunL75
import EquivLean.Modernize.Cbtrn02c.JavaTermRunL83
import EquivLean.Modernize.Cbtrn02c.Any.JavaRun

/-!
# CBTRN02C → Java on any input: `run` terminates, and is totally correct

`run_thin` collects the thin VCs of `run` (the entry path and the cut points 12, 22, 35, 44, 48, 65,
75, 83), assembled from the thin twins of the segments as `run_vcX` is from the segments; with
`run_vcX` it gives the termination VC (`Jimple.TermVC.of_thin`), and with the callee contracts
(valid, `runCX_valid`; terminating, `runCX_term`) termination for fixed inputs (`run_termG`,
`Jimple.TermVC.mterm`). `Any.Java.run_term`: on every input of `runSpec`, the inputs read off the
heap fix the ghost values (as in `Any.Java.run_sat`). `Any.Java.run_total`: with `run_sat`, every
call of `run` on inputs of `runSpec` has an outcome and every outcome satisfies `runSpec`
(`Jimple.total_of_sat_mterm`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem run_thin (g : G) :
    ThinVC Gen.prog runCX.env 1 Any.Java.runRef (runSpecGX g) (runInvX g) runVs 60 := by
  refine ⟨runBodyT, rfl, ?_⟩
  intro args σ0 hpre
  have hpre0 := hpre
  obtain ⟨rfl, -, -⟩ := hpre0
  have hn : ∀ (G' : Nat × (List Value → State → Frame → State → Prop) → Frame → State → Prop)
      (k : Nat), k ∉ [12, 22, 35, 44, 48, 65, 75, 83] →
      ((runInvX g).map fun q => (q.1, G' q)).lookup k = none :=
    fun G' k h => lookup_map_key_none G' (runInvX g) k (runInvX_keys g k h)
  refine ⟨?_, ?_⟩
  · have h0 : ((runInvX g).inst g.args σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← RunThinWPcX_eq g σ0]
    exact run_tseg0 g σ0 _ hpre
      (hn _ 1 (by decide)) (hn _ 2 (by decide)) (hn _ 3 (by decide)) (hn _ 4 (by decide))
      (hn _ 5 (by decide)) (hn _ 6 (by decide)) (hn _ 7 (by decide)) (hn _ 8 (by decide))
      (hn _ 9 (by decide)) (hn _ 10 (by decide)) (hn _ 11 (by decide)) rfl
  · intro p hp fr σ hI
    rw [← RunThinWPcX_eq g σ0]
    simp only [runInvX, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact run_tseg12 g σ0 fr σ _ hpre hI
        (hn _ 13 (by decide)) (hn _ 14 (by decide)) (hn _ 15 (by decide)) (hn _ 16 (by decide))
        (hn _ 17 (by decide)) (hn _ 18 (by decide)) (hn _ 19 (by decide)) (hn _ 20 (by decide))
        (hn _ 21 (by decide)) rfl rfl
    · exact run_tseg22 g σ0 fr σ _ hpre hI
        (hn _ 23 (by decide)) (hn _ 24 (by decide)) (hn _ 25 (by decide)) (hn _ 26 (by decide))
        (hn _ 27 (by decide)) (hn _ 28 (by decide)) (hn _ 29 (by decide)) (hn _ 30 (by decide))
        (hn _ 31 (by decide)) (hn _ 32 (by decide)) (hn _ 33 (by decide)) (hn _ 34 (by decide))
        rfl rfl
    · exact run_tseg35 g σ0 fr σ _ hpre hI
        (hn _ 36 (by decide)) (hn _ 37 (by decide)) (hn _ 38 (by decide)) (hn _ 39 (by decide))
        (hn _ 40 (by decide)) (hn _ 41 (by decide)) (hn _ 42 (by decide)) (hn _ 43 (by decide)) rfl
    · exact run_tseg44 g σ0 fr σ _ hpre hI
        (hn _ 45 (by decide)) (hn _ 46 (by decide)) (hn _ 47 (by decide)) rfl
    · exact run_tseg48 g σ0 fr σ _ hpre hI
        (hn _ 49 (by decide)) (hn _ 50 (by decide)) (hn _ 51 (by decide)) (hn _ 52 (by decide))
        (hn _ 53 (by decide)) (hn _ 54 (by decide)) (hn _ 55 (by decide)) (hn _ 56 (by decide))
        (hn _ 57 (by decide)) (hn _ 58 (by decide)) (hn _ 59 (by decide)) (hn _ 60 (by decide))
        (hn _ 61 (by decide)) (hn _ 62 (by decide)) (hn _ 63 (by decide)) (hn _ 64 (by decide)) rfl
    · exact run_tseg65 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn _ k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega))
        rfl rfl rfl
    · exact run_tseg75 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn _ k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega))
        rfl
    · exact run_tseg83 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn _ k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega))

/-- The callee contracts of `run` terminate. -/
theorem runCX_term :
    ∀ sig S, (runCX.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    intro p hp
    simp only [runCX, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact copyAccountF_cterm
    · exact copyTcatF_cterm
    · exact spaces_cterm
    · exact ctorXR_cterm
    · exact ctorAC_cterm
    · exact ctorTC_cterm
    · exact ctorTR_cterm
    · exact padNum_cterm
    · exact validateTran_cterm
    · exact writeReject_cterm
    · exact postTransaction_cterm) _ _

/-- `run` terminates, for the contract with fixed inputs. -/
theorem run_termG (g : G) :
    ∀ args σ, (runSpecGX g).pre args σ → MTerm Gen.prog Any.Java.runRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) runCX_valid runCX_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (run_vcX g) (run_thin g))

end EquivLean.Modernize.Cbtrn02c.Java

namespace EquivLean.Modernize.Cbtrn02c.Any.Java

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Cbtrn02c.Java.Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨v1, v2, v3, v4, clk, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  have hin0 := hin
  obtain ⟨a1, a2, a3, a4, cs, hargs, -⟩ := hin0
  have hpreG : Cbtrn02c.Java.RunPreGX ⟨a1, a2, a3, a4, cs, v1, v2, v3, v4, clk⟩ args σ := by
    refine ⟨hargs, ?_, ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩⟩
    rw [hargs] at hin
    exact hin
  exact Cbtrn02c.Java.run_termG ⟨a1, a2, a3, a4, cs, v1, v2, v3, v4, clk⟩ args σ hpreG

/-- **CBTRN02C → Java on any input, total correctness**: on every input of `runSpec`, `run` has an
    outcome, and every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Cbtrn02c.Java.Gen.prog runRef args σ o) ∧
      ∀ o, MExec Cbtrn02c.Java.Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.Cbtrn02c.Any.Java

#print axioms EquivLean.Modernize.Cbtrn02c.Any.Java.run_term
#print axioms EquivLean.Modernize.Cbtrn02c.Any.Java.run_total
