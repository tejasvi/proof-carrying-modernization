-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermRun.lean (sha256 77ae934088a5ef6b...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRun
import EquivLean.Modernize.Cbact04c.Every.JavaTermLink
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg0c
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg10c
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg28c
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg38a
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg42
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg47
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg57
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg63
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg70
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg85i
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg85x
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg89b
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg97s
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg97n
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg97p
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg102
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg108
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg113
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg125
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg129
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg129m
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg148
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg148n
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg148f
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg172
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg172d
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg184
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg196z
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg196n
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg199
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg210
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg217
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg224
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg232
import EquivLean.Modernize.Cbact04c.Every.JavaTermSeg242

/-!
# CBACT04C → Java on every input: `run` terminates, and is totally correct

`run_thin` collects the thin VCs of `run` as `run_vc` (`Every.JavaRun`) collects its VCs: the
entry path and the paths from each cut point of `runInvE` (`runInv` and the `DEFAULT` retry, 184:
the thin twins `run_tseg*` of the segment theorems, with the offset `B = 2^32` of `runVs`), by the
same case analyses. With `run_vc` it gives the termination VC (`Jimple.TermVC.of_thin`), and with
the callee contracts (valid, `runC_valid`; terminating, `runC_term`) termination for fixed ghosts
(`run_termG`, `Jimple.TermVC.mterm`). In `Every.Java`, `run_term` takes the ghosts from the
precondition as `run_sat` does, and `run_total`: with `run_sat`, every call of `run` on inputs of
`runSpec` has an outcome, and every outcome satisfies `runSpec` (`Jimple.total_of_sat_mterm`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- The thin cut list of `run` from cut point `pc` (frame `fr`, state `σ`): each cut point's
    variant below the value at `(pc, fr, σ)`. -/
abbrev runTCuts (g : G) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Cuts :=
  (runInvE g).map fun q => (q.1, fun fr' σ' =>
    runVs 4294967296 q.1 g.args σ0 fr' σ' < runVs 4294967296 pc g.args σ0 fr σ)

/- The thin VCs are applied as they are stated: `bodyWP` must not be unfolded (and evaluated)
when they are matched against `ThinVC`. -/
attribute [local irreducible] bodyWP

set_option maxRecDepth 4000 in
theorem run_thin (g : G) :
    ThinVC Gen.prog runC.env 1 runRef (runSpecG g) (runInvE g) (runVs 4294967296) 60 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0 hpre
  have hargs : args = g.args := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have hl : ((runInvE g).inst g.args σ0).lookup 0 = none := rfl
    have h : RunThinWPc g σ0 ((runInvE g).map fun p => (p.1, fun _ _ => True)) 0
        (Frame.init true g.args) σ0 := by
      apply run_tseg0 g σ0 _ 4294967296 (by decide) (by decide) hpre <;> rfl
    unfold RunThinWPc at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInvE, runInv, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- 10
    · have h : RunThinWPc g σ0 (runTCuts g σ0 10 fr σ) 10 fr σ := by
        apply run_tseg10 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 28
    · have h : RunThinWPc g σ0 (runTCuts g σ0 28 fr σ) 28 fr σ := by
        apply run_tseg28 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 38
    · have h : RunThinWPc g σ0 (runTCuts g σ0 38 fr σ) 38 fr σ := by
        apply run_tseg38 g σ0 fr σ _ 4294967296 (by decide) (by decide) hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 42
    · have h : RunThinWPc g σ0 (runTCuts g σ0 42 fr σ) 42 fr σ := by
        apply run_tseg42 g σ0 fr σ _ 4294967296 (by decide) (by decide) hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 47
    · have h : RunThinWPc g σ0 (runTCuts g σ0 47 fr σ) 47 fr σ := by
        apply run_tseg47 g σ0 fr σ _ 4294967296 (by decide) (by decide) hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 57
    · have h : RunThinWPc g σ0 (runTCuts g σ0 57 fr σ) 57 fr σ := by
        apply run_tseg57 g σ0 fr σ _ 4294967296 (by decide) (by decide) hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 63
    · have h : RunThinWPc g σ0 (runTCuts g σ0 63 fr σ) 63 fr σ := by
        apply run_tseg63 g σ0 fr σ _ 4294967296 (by decide) (by decide) hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 70
    · have h : RunThinWPc g σ0 (runTCuts g σ0 70 fr σ) 70 fr σ := by
        apply run_tseg70 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 85: the next record or the end
    · obtain ⟨i, -, -, -, -, -, -, -, f22, -⟩ := id hJ
      rcases Int.lt_or_le i.toInt (g.tcat.length : Int) with hlt | hge
      · have h : RunThinWPc g σ0 (runTCuts g σ0 85 fr σ) 85 fr σ := by
          apply run_tseg85_iter g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
            (fun i' h' => by rw [← eq_of_get f22 h']; exact hlt) <;> rfl
        unfold RunThinWPc at h; exact h
      · have h : RunThinWPc g σ0 (runTCuts g σ0 85 fr σ) 85 fr σ := by
          apply run_tseg85_exit g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
            (fun i' h' => by rw [← eq_of_get f22 h']; exact hge) <;> rfl
        unfold RunThinWPc at h; exact h
    -- 90
    · have h : RunThinWPc g σ0 (runTCuts g σ0 90 fr σ) 90 fr σ := by
        apply run_tseg90 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 97: the first record, the same account, or a new account
    · obtain ⟨i, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      rcases hl : (g.st i.toInt.toNat).lastId with _ | id
      · have h : RunThinWPc g σ0 (runTCuts g σ0 97 fr σ) 97 fr σ := by
          apply run_tseg97_first g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hl) <;> rfl
        unfold RunThinWPc at h; exact h
      · by_cases he : id = Model.tAcct (g.trec i.toInt.toNat)
        · have h : RunThinWPc g σ0 (runTCuts g σ0 97 fr σ) 97 fr σ := by
            apply run_tseg97_same g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
              (fun i' h' => by rw [← eq_of_get1 f22 h', hl, he]) <;> rfl
          unfold RunThinWPc at h; exact h
        · have h : RunThinWPc g σ0 (runTCuts g σ0 97 fr σ) 97 fr σ := by
            apply run_tseg97_post g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
              (fun i' h' => by
                rw [← eq_of_get1 f22 h', hl]
                exact ⟨rfl, fun e => he (Option.some.inj e)⟩) <;> rfl
          unfold RunThinWPc at h; exact h
    -- 102
    · have h : RunThinWPc g σ0 (runTCuts g σ0 102 fr σ) 102 fr σ := by
        apply run_tseg102 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 108
    · have h : RunThinWPc g σ0 (runTCuts g σ0 108 fr σ) 108 fr σ := by
        apply run_tseg108 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 113
    · have h : RunThinWPc g σ0 (runTCuts g σ0 113 fr σ) 113 fr σ := by
        apply run_tseg113 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 125
    · have h : RunThinWPc g σ0 (runTCuts g σ0 125 fr σ) 125 fr σ := by
        apply run_tseg125 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 129: the account found or missing
    · obtain ⟨i, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      by_cases hex : ∃ a ∈ (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts,
          Model.aId a = Model.tAcct (g.trec i.toInt.toNat)
      · have h : RunThinWPc g σ0 (runTCuts g σ0 129 fr σ) 129 fr σ := by
          apply run_tseg129_found g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hex
          all_goals rfl
        unfold RunThinWPc at h; exact h
      · have h : RunThinWPc g σ0 (runTCuts g σ0 129 fr σ) 129 fr σ := by
          apply run_tseg129_missing g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hex
          all_goals rfl
        unfold RunThinWPc at h; exact h
    -- 148: the cross-reference search ends, goes on, or finds the account
    · obtain ⟨i, -, -, -, -, k, ⟨-, -, -, f22, -⟩, -, -, -, -, -, -, -, -, f23, -⟩ := id hJ
      rcases (Int.lt_or_le k.toInt (g.xrefs.length : Int)).symm with hle | hlt
      · have h : RunThinWPc g σ0 (runTCuts g σ0 148 fr σ) 148 fr σ := by
          apply run_tseg148_exit g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' k' _ h23 => by rw [← eq_of_get f23 h23]; exact hle
          all_goals rfl
        unfold RunThinWPc at h; exact h
      · by_cases he : ∀ hk : k.toInt.toNat < g.xrefs.length,
            Model.xAcct (g.xrefs[k.toInt.toNat]) = Model.tAcct (g.trec i.toInt.toNat)
        · have h : RunThinWPc g σ0 (runTCuts g σ0 148 fr σ) 148 fr σ := by
            apply run_tseg148_found g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
              (fun i' k' h22 h23 => by
                rw [← eq_of_get1 f22 h22, ← eq_of_get f23 h23]; exact ⟨hlt, he⟩) <;> rfl
          unfold RunThinWPc at h; exact h
        · have h : RunThinWPc g σ0 (runTCuts g σ0 148 fr σ) 148 fr σ := by
            apply run_tseg148_next g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
              (fun i' k' h22 h23 => by
                rw [← eq_of_get1 f22 h22, ← eq_of_get f23 h23]
                exact ⟨hlt, fun hk e => he (fun _ => e)⟩) <;> rfl
          unfold RunThinWPc at h; exact h
    -- 172: the account's group has a record, or the DEFAULT retry
    · obtain ⟨i, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      cases hgm : grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
          (g.trec i.toInt.toNat) with
      | false =>
        have h : RunThinWPc g σ0 (runTCuts g σ0 172 fr σ) 172 fr σ := by
          apply run_tseg172 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hgm
          all_goals rfl
        unfold RunThinWPc at h; exact h
      | true =>
        have h : RunThinWPc g σ0 (runTCuts g σ0 172 fr σ) 172 fr σ := by
          apply run_tseg172_dflt g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hgm
          all_goals rfl
        unfold RunThinWPc at h; exact h
    -- 196: rate zero or not
    · obtain ⟨i, -, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      by_cases hr : Model.dRate (discD g (stSel g.xrefs (g.st i.toInt.toNat)
          (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat)) = 0
      · have h : RunThinWPc g σ0 (runTCuts g σ0 196 fr σ) 196 fr σ := by
          apply run_tseg196_zero g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hr) <;> rfl
        unfold RunThinWPc at h; exact h
      · have h : RunThinWPc g σ0 (runTCuts g σ0 196 fr σ) 196 fr σ := by
          apply run_tseg196_rate g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hr) <;> rfl
        unfold RunThinWPc at h; exact h
    -- 199
    · have h : RunThinWPc g σ0 (runTCuts g σ0 199 fr σ) 199 fr σ := by
        apply run_tseg199 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 210
    · have h : RunThinWPc g σ0 (runTCuts g σ0 210 fr σ) 210 fr σ := by
        apply run_tseg210 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 217
    · have h : RunThinWPc g σ0 (runTCuts g σ0 217 fr σ) 217 fr σ := by
        apply run_tseg217 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 224
    · have h : RunThinWPc g σ0 (runTCuts g σ0 224 fr σ) 224 fr σ := by
        apply run_tseg224 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 232
    · have h : RunThinWPc g σ0 (runTCuts g σ0 232 fr σ) 232 fr σ := by
        apply run_tseg232 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 242
    · have h : RunThinWPc g σ0 (runTCuts g σ0 242 fr σ) 242 fr σ := by
        apply run_tseg242 g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ <;> rfl
      unfold RunThinWPc at h; exact h
    -- 184: the DEFAULT group's record, or the abend
    · obtain ⟨i, -, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      by_cases hd : defDisc g (g.trec i.toInt.toNat) = []
      · have h : RunThinWPc g σ0 (runTCuts g σ0 184 fr σ) 184 fr σ := by
          apply run_tseg184_missing g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hd
          all_goals rfl
        unfold RunThinWPc at h; exact h
      · have h : RunThinWPc g σ0 (runTCuts g σ0 184 fr σ) 184 fr σ := by
          apply run_tseg184_found g σ0 fr σ _ 4294967296 (by decide) (by decide) hpre hJ
          case hc => exact fun i' h' => by rw [← eq_of_get1 f22 h']; exact hd
          all_goals rfl
        unfold RunThinWPc at h; exact h

/-- `run` terminates, for the contract with fixed ghost values. -/
theorem run_termG (g : G) :
    ∀ args σ, (runSpecG g).pre args σ → MTerm Gen.prog runRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) runC_valid runC_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (run_vc g) (run_thin g))

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Every.Java

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

/-- **`run` terminates** on every input of `Every.Java.runSpec` (the ghosts from the precondition,
    as in `run_sat`). -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Cbact04c.Java.Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨vals1, vals2, vals3, vals4, link1, clk, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  have hinits : Cbact04c.Java.Inits σ := ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  obtain ⟨a1, a2, a3, a4, p1, cs, hargs, -⟩ := id hin
  subst hargs
  exact Cbact04c.Java.run_termG ⟨a1, a2, a3, a4, p1, cs, vals1, vals2, vals3, vals4, link1, clk⟩ _ σ
    ⟨rfl, hin, hinits⟩

/-- **CBACT04C → Java on every input, total correctness**: on every input of `runSpec`, `run` has
    an outcome, and every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Cbact04c.Java.Gen.prog runRef args σ o) ∧
      ∀ o, MExec Cbact04c.Java.Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.Cbact04c.Every.Java

#print axioms EquivLean.Modernize.Cbact04c.Every.Java.run_term
#print axioms EquivLean.Modernize.Cbact04c.Every.Java.run_total
