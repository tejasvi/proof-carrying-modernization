import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Aeneas.SumPR

/-!
# Loop unrolling: an asynchronous (stuttering) product of two Aeneas loops

`sumpr.v4.sum` (PR 3 in `examples/rust/sumpr/src/lib.rs`) unrolls the summation loop of
`sumpr.v1.sum` by two: one iteration adds `v[i]` and, if `i + 1 < len`, also `v[i + 1]`.  The
iterations do not correspond one to one, so the loops are aligned by a scheduler
(`sim_loop_stutter`, core):

* phase A (same state): if the next pair can be added without overflow, the source alone runs
  one iteration (`right`), reaching phase B; otherwise both run one iteration (`both`: both
  leave with the same overflow panic, or both stop at the end, or both add the last element);
* phase B (source one element ahead): both run one iteration (`both`) and are in phase A
  again, or, at the end of the slice, the target alone catches up (`left`).

This gives `v4_sim_v1`; with the safety of the source (`SumPR.v1_spec`) it is the equivalence
`v4_equiv_v1`, panics included: the unrolled loop overflows on exactly the same inputs.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.SumUnroll

/-- The element at `i` as a number (`0` outside the slice). -/
def el (v : Slice U32) (i : Nat) : Nat := (v.val.getD i 0#u32).val

theorem el_eq (v : Slice U32) (i : Nat) (h : i < v.val.length) : el v i = (v.val[i]).val := by
  simp [el, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Coupling of a target state (`v4`) with a source state (`v1`): phase A or phase B. -/
def Inv (v : Slice U32) (p q : U32 × Usize) : Prop :=
  p.2.val ≤ v.val.length ∧ q.2.val ≤ v.val.length ∧
    ((p.1 = q.1 ∧ p.2 = q.2) ∨
     (q.2.val = p.2.val + 1 ∧ p.2.val < v.val.length ∧ q.1.val = p.1.val + el v p.2.val))

/-- The variant: the elements that remain on both sides. -/
def Var (v : Slice U32) (p q : U32 × Usize) : Nat :=
  (v.val.length - p.2.val) + (v.val.length - q.2.val)

/-- The scheduler. -/
def sched (v : Slice U32) (p q : U32 × Usize) : Sched :=
  if p.2 = q.2 then
    (if p.2.val + 1 < v.val.length ∧ p.1.val + el v p.2.val ≤ 4294967295 then .right else .both)
  else (if q.2.val < v.val.length then .both else .left)

/-- The two loop bodies, as the generated `loop` calls see them. -/
abbrev B4 (v : Slice U32) := fun (x : U32 × Usize) => sumpr.v4.sum_loop.body v x.1 x.2
abbrev B1 (v : Slice U32) := fun (x : U32 × Usize) => sumpr.v1.sum_loop.body v x.1 x.2

set_option maxHeartbeats 1000000 in
theorem step_both (v : Slice U32) (p q : U32 × Usize) (hI : Inv v p q)
    (hs : sched v p q = .both) :
    Sim (StepRel loopCls loopCls (· = ·) (fun p' q' => Inv v p' q' ∧ Var v p' q' < Var v p q))
      (B4 v p) (B1 v q) := by
  obtain ⟨s4, i4⟩ := p
  obtain ⟨s1, i1⟩ := q
  obtain ⟨h4, h1, hph⟩ := hI
  simp only [Inv, Var, sched] at h4 h1 hph hs ⊢
  apply sim_of_wp
  have hlen := v.property
  rcases hph with ⟨rfl, rfl⟩ | ⟨hi, hlt, hs1⟩
  · by_cases hc : i4.val + 1 < v.val.length ∧ s4.val + el v i4.val ≤ 4294967295
    · simp [hc] at hs
    · clear hs
      by_cases hl : i4.val < v.val.length
      · rw [el_eq v _ hl] at hc
        aeneas_wp [sumpr.v4.sum_loop.body, sumpr.v1.sum_loop.body] at ⊢
        aeneas_leaves
      · aeneas_wp [sumpr.v4.sum_loop.body, sumpr.v1.sum_loop.body] at ⊢
        aeneas_leaves
  · have hne : ¬ i4 = i1 := fun h => by rw [h] at hi; omega
    by_cases hC : i1.val < v.val.length
    · clear hs
      rw [el_eq v _ hlt] at hs1
      aeneas_wp [sumpr.v4.sum_loop.body, sumpr.v1.sum_loop.body] at ⊢
      aeneas_leaves
    · simp [hne, hC] at hs

theorem step_left (v : Slice U32) (p q : U32 × Usize) (hI : Inv v p q)
    (hs : sched v p q = .left) :
    wp (B4 v p) (fun r => ∃ p', loopCls r = .inr p' ∧ Inv v p' q ∧ Var v p' q < Var v p q) := by
  obtain ⟨s4, i4⟩ := p
  obtain ⟨s1, i1⟩ := q
  obtain ⟨h4, h1, hph⟩ := hI
  simp only [Inv, Var, sched] at h4 h1 hph hs ⊢
  have hlen := v.property
  rcases hph with ⟨rfl, rfl⟩ | ⟨hi, hlt, hs1⟩
  · by_cases hc : i4.val + 1 < v.val.length ∧ s4.val + el v i4.val ≤ 4294967295 <;>
      simp [hc] at hs
  · have hne : ¬ i4 = i1 := fun h => by rw [h] at hi; omega
    by_cases hC : i1.val < v.val.length
    · simp [hne, hC] at hs
    · clear hs
      rw [el_eq v _ hlt] at hs1
      aeneas_wp [sumpr.v4.sum_loop.body] at ⊢
      aeneas_leaves

theorem step_right (v : Slice U32) (p q : U32 × Usize) (hI : Inv v p q)
    (hs : sched v p q = .right) :
    wp (B1 v q) (fun r => ∃ q', loopCls r = .inr q' ∧ Inv v p q' ∧ Var v p q' < Var v p q) := by
  obtain ⟨s4, i4⟩ := p
  obtain ⟨s1, i1⟩ := q
  obtain ⟨h4, h1, hph⟩ := hI
  simp only [Inv, Var, sched] at h4 h1 hph hs ⊢
  have hlen := v.property
  rcases hph with ⟨rfl, rfl⟩ | ⟨hi, hlt, hs1⟩
  · by_cases hc : i4.val + 1 < v.val.length ∧ s4.val + el v i4.val ≤ 4294967295
    · clear hs
      have hl : i4.val < v.val.length := by omega
      have hel := el_eq v _ hl
      aeneas_wp [sumpr.v1.sum_loop.body] at ⊢
      aeneas_leaves
    · simp [hc] at hs
  · have hne : ¬ i4 = i1 := fun h => by rw [h] at hi; omega
    by_cases hC : i1.val < v.val.length <;> simp [hne, hC] at hs

theorem v4_sim_v1 (v : Slice U32) : Sim (· = ·) (sumpr.v4.sum v) (sumpr.v1.sum v) := by
  simp only [sumpr.v4.sum, sumpr.v1.sum, sumpr.v4.sum_loop, sumpr.v1.sum_loop]
  exact sim_loop_stutter (loop_shape (B4 v)) (loop_shape (B1 v)) (Inv v) (Var v) (sched v)
    (fun p q hI hs => step_both v p q hI hs) (fun p q hI hs => step_left v p q hI hs)
    (fun p q hI hs _ => step_right v p q hI hs) _ _ ⟨by simp, by simp, .inl ⟨rfl, rfl⟩⟩

/-- The unrolled loop is equivalent to the original, panics included. -/
theorem v4_equiv_v1 (v : Slice U32) : Equiv (· = ·) (sumpr.v4.sum v) (sumpr.v1.sum v) :=
  equiv_of_sim_of_safe (v4_sim_v1 v) (SumPR.v1_spec v).1

end EquivLean.Demo.Aeneas.SumUnroll

#print axioms EquivLean.Demo.Aeneas.SumUnroll.v4_equiv_v1
