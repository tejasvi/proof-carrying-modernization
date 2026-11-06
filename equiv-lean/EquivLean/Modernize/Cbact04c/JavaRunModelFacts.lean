import EquivLean.Modernize.Cbact04c.JavaSpec

/-!
# CBACT04C: facts about `Model.run` used by the Java proof

The account table keeps its ids and groups under the rewrites, the current account and
cross-reference are the lookups of the last account id, the running total stays below
`10^11` and the transaction suffix below `10^6`.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Model

/-! ## Lists -/

theorem replaceFirst_length {α : Type} (p : α → Bool) (x : α) :
    ∀ l : List α, (replaceFirst p x l).length = l.length
  | [] => rfl
  | y :: ys => by
    simp only [replaceFirst]
    split <;> simp [replaceFirst_length p x ys]

/-- `replaceFirst` replaces the first match: the list with that position set. -/
theorem replaceFirst_eq_set {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), p l[i] = true → (∀ j (hj : j < i), p (l[j]'(by omega)) = false) →
      replaceFirst p x l = l.set i x
  | [], i, hi, _, _ => by simp at hi
  | y :: ys, 0, _, hp, _ => by simp [replaceFirst] at hp ⊢; simp [hp]
  | y :: ys, i + 1, hi, hp, hj => by
    have h0 := hj 0 (by omega)
    simp only [List.getElem_cons_zero] at h0
    simp only [replaceFirst, h0, Bool.false_eq_true, ↓reduceIte, List.set_cons_succ]
    congr 1
    exact replaceFirst_eq_set p x ys i (by simpa using hi) (by simpa using hp)
      (fun j hj' => by simpa using hj (j + 1) (by omega))

/-- `find?` is the first match. -/
theorem find?_eq_getElem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), p l[i] = true →
      (∀ j (hj : j < i), p (l[j]'(by omega)) = false) → l.find? p = some l[i]
  | [], i, hi, _, _ => by simp at hi
  | y :: ys, 0, _, hp, _ => by simp at hp ⊢; simp [hp]
  | y :: ys, i + 1, hi, hp, hj => by
    have h0 := hj 0 (by omega)
    simp only [List.getElem_cons_zero] at h0
    rw [List.find?_cons_of_neg (by simp [h0])]
    exact find?_eq_getElem p ys i (by simpa using hi) (by simpa using hp)
      (fun j hj' => by simpa using hj (j + 1) (by omega))

/-- An element satisfying `p` gives a first one. -/
theorem exists_first {α : Type} (p : α → Bool) (l : List α) (h : ∃ a ∈ l, p a = true) :
    ∃ i, ∃ hi : i < l.length, p l[i] = true ∧ ∀ j (hj : j < i), p (l[j]'(by omega)) = false := by
  induction l with
  | nil => obtain ⟨a, ha, -⟩ := h; simp at ha
  | cons y ys ih =>
    by_cases hy : p y = true
    · exact ⟨0, by simp only [List.length_cons]; omega, by simpa using hy,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · obtain ⟨a, ha, hpa⟩ := h
      have ha' : a ∈ ys := by
        rcases List.mem_cons.1 ha with rfl | h
        · exact absurd hpa hy
        · exact h
      obtain ⟨i, hi, hp, hj⟩ := ih ⟨a, ha', hpa⟩
      refine ⟨i + 1, by simpa using hi, by simpa using hp, fun j hj' => ?_⟩
      cases j with
      | zero => simpa using hy
      | succ j => simpa using hj j (by omega)

end EquivLean.Modernize.Cbact04c.Model
