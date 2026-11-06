import EquivLean.Modernize.Cbact04c.JavaProof
import EquivLean.Modernize.Cbact04c.JavaRunOks
import EquivLean.Modernize.Cbact04c.JavaRunSeg0c
import EquivLean.Modernize.Cbact04c.JavaRunSeg10c
import EquivLean.Modernize.Cbact04c.JavaRunSeg28c
import EquivLean.Modernize.Cbact04c.JavaRunSeg38a
import EquivLean.Modernize.Cbact04c.JavaRunSeg42
import EquivLean.Modernize.Cbact04c.JavaRunSeg47
import EquivLean.Modernize.Cbact04c.JavaRunSeg57
import EquivLean.Modernize.Cbact04c.JavaRunSeg63
import EquivLean.Modernize.Cbact04c.JavaRunSeg70
import EquivLean.Modernize.Cbact04c.JavaRunSeg85i
import EquivLean.Modernize.Cbact04c.JavaRunSeg85x
import EquivLean.Modernize.Cbact04c.JavaRunSeg89b
import EquivLean.Modernize.Cbact04c.JavaRunSeg97s
import EquivLean.Modernize.Cbact04c.JavaRunSeg97n
import EquivLean.Modernize.Cbact04c.JavaRunSeg97p
import EquivLean.Modernize.Cbact04c.JavaRunSeg102
import EquivLean.Modernize.Cbact04c.JavaRunSeg108
import EquivLean.Modernize.Cbact04c.JavaRunSeg113
import EquivLean.Modernize.Cbact04c.JavaRunSeg125
import EquivLean.Modernize.Cbact04c.JavaRunSeg129
import EquivLean.Modernize.Cbact04c.JavaRunSeg148
import EquivLean.Modernize.Cbact04c.JavaRunSeg148n
import EquivLean.Modernize.Cbact04c.JavaRunSeg148f
import EquivLean.Modernize.Cbact04c.JavaRunSeg172
import EquivLean.Modernize.Cbact04c.JavaRunSeg196z
import EquivLean.Modernize.Cbact04c.JavaRunSeg196n
import EquivLean.Modernize.Cbact04c.JavaRunSeg199
import EquivLean.Modernize.Cbact04c.JavaRunSeg210
import EquivLean.Modernize.Cbact04c.JavaRunSeg217
import EquivLean.Modernize.Cbact04c.JavaRunSeg224
import EquivLean.Modernize.Cbact04c.JavaRunSeg232
import EquivLean.Modernize.Cbact04c.JavaRunSeg242

/-!
# CBACT04C → Java: `run` satisfies its contract, hence the generated statement

`run_vc` collects the verification conditions of `run`: the entry path and the paths from each
cut point of `runInv` (segment theorems `run_seg*`, stated for any cut list with the lookups they
pass through); the callees are answered by their contracts `runC` (valid by `runC_valid`).
`run_sat` is the contract `runSpec` of `JavaSpec.lean`, and `java : Statement` follows by
`statement_of_sat`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbact04c.Java

theorem eq_of_get {fr : Frame} {k : Nat} {a b : I32} (ha : fr.get k = some (.int a))
    (hb : fr.get k = some (.int b)) : a = b := by
  rw [ha] at hb
  simpa using hb

theorem eq_of_get1 {fr : Frame} {k : Nat} {a b : I32} (ha : fr.get k = some (.int (a + 1#32)))
    (hb : fr.get k = some (.int (b + 1#32))) : a = b := by
  have e := eq_of_get ha hb
  have := congrArg (fun x => x - 1#32) e
  simpa using this

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded
(and evaluated) when they are matched against `MethodVC`. -/
attribute [local irreducible] bodyWP

theorem run_isStatic : runRef.decl.mods.isStatic = true := rfl

set_option maxRecDepth 4000 in
theorem run_vc (g : G) : MethodVC Gen.prog runC.env 1 runRef (runSpecG g) (runInv g) 60 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0 hpre
  have hargs : args = g.args := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have hl : ((runInv g).inst g.args σ0).lookup 0 = none := rfl
    have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 0 (Frame.init true g.args) σ0 := by
      apply run_seg0 g σ0 _ hpre <;> rfl
    unfold RunWPc at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- 10
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 10 fr σ := by
        apply run_seg10 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 28
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 28 fr σ := by
        apply run_seg28 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 38
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 38 fr σ := by
        apply run_seg38 g σ0 fr σ _ hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 42
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 42 fr σ := by
        apply run_seg42 g σ0 fr σ _ hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 47
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 47 fr σ := by
        apply run_seg47 g σ0 fr σ _ hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 57
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 57 fr σ := by
        apply run_seg57 g σ0 fr σ _ hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 63
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 63 fr σ := by
        apply run_seg63 g σ0 fr σ _ hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 70
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 70 fr σ := by
        apply run_seg70 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 85: the next record or the end
    · obtain ⟨i, -, -, -, -, -, -, -, f22, -⟩ := id hJ
      rcases Int.lt_or_le i.toInt (g.tcat.length : Int) with hlt | hge
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 85 fr σ := by
          apply run_seg85_iter g σ0 fr σ _ hpre hJ
            (fun i' h' => by rw [← eq_of_get f22 h']; exact hlt) <;> rfl
        unfold RunWPc at h; exact h
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 85 fr σ := by
          apply run_seg85_exit g σ0 fr σ _ hpre hJ
            (fun i' h' => by rw [← eq_of_get f22 h']; exact hge) <;> rfl
        unfold RunWPc at h; exact h
    -- 90
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 90 fr σ := by
        apply run_seg90 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 97: the first record, the same account, or a new account
    · obtain ⟨i, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      rcases hl : (g.st i.toInt.toNat).lastId with _ | id
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 97 fr σ := by
          apply run_seg97_first g σ0 fr σ _ hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hl) <;> rfl
        unfold RunWPc at h; exact h
      · by_cases he : id = Model.tAcct (g.trec i.toInt.toNat)
        · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 97 fr σ := by
            apply run_seg97_same g σ0 fr σ _ hpre hJ
              (fun i' h' => by rw [← eq_of_get1 f22 h', hl, he]) <;> rfl
          unfold RunWPc at h; exact h
        · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 97 fr σ := by
            apply run_seg97_post g σ0 fr σ _ hpre hJ
              (fun i' h' => by
                rw [← eq_of_get1 f22 h', hl]
                exact ⟨rfl, fun e => he (Option.some.inj e)⟩) <;> rfl
          unfold RunWPc at h; exact h
    -- 102
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 102 fr σ := by
        apply run_seg102 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 108
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 108 fr σ := by
        apply run_seg108 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 113
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 113 fr σ := by
        apply run_seg113 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 125
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 125 fr σ := by
        apply run_seg125 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 129
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 129 fr σ := by
        apply run_seg129 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 148: the cross-reference search ends, goes on, or finds the account
    · obtain ⟨i, -, -, -, -, k, ⟨-, -, -, f22, -⟩, -, -, -, -, -, -, -, -, f23, -⟩ := id hJ
      rcases (Int.lt_or_le k.toInt (g.xrefs.length : Int)).symm with hle | hlt
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 148 fr σ := by
          apply run_seg148_exit g σ0 fr σ _ hpre hJ
            (fun i' k' _ h23 => by rw [← eq_of_get f23 h23]; exact hle) <;> rfl
        unfold RunWPc at h; exact h
      · by_cases he : ∀ hk : k.toInt.toNat < g.xrefs.length,
            Model.xAcct (g.xrefs[k.toInt.toNat]) = Model.tAcct (g.trec i.toInt.toNat)
        · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 148 fr σ := by
            apply run_seg148_found g σ0 fr σ _ hpre hJ
              (fun i' k' h22 h23 => by
                rw [← eq_of_get1 f22 h22, ← eq_of_get f23 h23]; exact ⟨hlt, he⟩) <;> rfl
          unfold RunWPc at h; exact h
        · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 148 fr σ := by
            apply run_seg148_next g σ0 fr σ _ hpre hJ
              (fun i' k' h22 h23 => by
                rw [← eq_of_get1 f22 h22, ← eq_of_get f23 h23]
                exact ⟨hlt, fun hk e => he (fun _ => e)⟩) <;> rfl
          unfold RunWPc at h; exact h
    -- 172
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 172 fr σ := by
        apply run_seg172 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 196: rate zero or not
    · obtain ⟨i, -, -, -, -, -, -, ⟨-, -, -, f22, -⟩, -⟩ := id hJ
      by_cases hr : Model.dRate (discOf g (stSel g.xrefs (g.st i.toInt.toNat)
          (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat)) = 0
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 196 fr σ := by
          apply run_seg196_zero g σ0 fr σ _ hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hr) <;> rfl
        unfold RunWPc at h; exact h
      · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 196 fr σ := by
          apply run_seg196_rate g σ0 fr σ _ hpre hJ
            (fun i' h' => by rw [← eq_of_get1 f22 h']; exact hr) <;> rfl
        unfold RunWPc at h; exact h
    -- 199
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 199 fr σ := by
        apply run_seg199 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 210
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 210 fr σ := by
        apply run_seg210 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 217
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 217 fr σ := by
        apply run_seg217 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 224
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 224 fr σ := by
        apply run_seg224 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 232
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 232 fr σ := by
        apply run_seg232 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h
    -- 242
    · have h : RunWPc g σ0 ((runInv g).inst g.args σ0) 242 fr σ := by
        apply run_seg242 g σ0 fr σ _ hpre hJ <;> rfl
      unfold RunWPc at h; exact h

/-- `run` against the contract with fixed ghost values. -/
theorem run_satG (g : G) : Sat Gen.prog runRef (runSpecG g) :=
  MethodVC.sat_of_valid runC_valid (run_vc g)

/-- **`run` returns the outputs of `Model.run`**: the contract `runSpec`. -/
theorem run_sat : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hm
  obtain ⟨vals1, vals2, vals3, vals4, link1, clk, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  have hinits : Inits σ := ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  obtain ⟨a1, a2, a3, a4, p1, cs, hargs, -⟩ := id hin
  subst hargs
  have h0 := run_satG ⟨a1, a2, a3, a4, p1, cs, vals1, vals2, vals3, vals4, link1, clk⟩ _ σ o
    ⟨rfl, hin, hinits⟩ hm
  cases o with
  | normal r σ' =>
    intro vals1' vals2' vals3' vals4' link1' clk' hin'
    exact run_satG ⟨a1, a2, a3, a4, p1, cs, vals1', vals2', vals3', vals4', link1', clk'⟩ _ σ _
      ⟨rfl, hin', hinits⟩ hm
  | exc e σ' => exact h0
  | wrong msg => exact h0

/-- **CBACT04C → Java**: the generated statement. -/
theorem java : Statement := statement_of_sat run_sat

end EquivLean.Modernize.Cbact04c.Java

#print axioms EquivLean.Modernize.Cbact04c.Java.run_sat
#print axioms EquivLean.Modernize.Cbact04c.Java.java
