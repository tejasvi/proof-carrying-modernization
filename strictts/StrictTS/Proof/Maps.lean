/-
StrictTS proof layer: laws of the `Map`/`Set` model.

`JSMap` is the specified insertion-ordered entry list with tombstones. For any key equality
that is an equivalence (SameValueZero is one), lookups after updates behave like a finite
map, while `toList` keeps the insertion order that JavaScript iteration observes.
-/
import StrictTS.Proof.Exec

namespace StrictTS
namespace JSMap

variable {K V : Type}

/-- A Boolean equivalence relation on keys. -/
structure Equiv (eq : K → K → Bool) : Prop where
  refl : ∀ a, eq a a = true
  symm : ∀ a b, eq a b = true → eq b a = true
  trans : ∀ a b c, eq a b = true → eq b c = true → eq a c = true

variable {eq : K → K → Bool}

theorem Equiv.congr_left (hE : Equiv eq) {a b c : K} (hab : eq a b = true) : eq a c = eq b c := by
  cases h1 : eq a c <;> cases h2 : eq b c
  · rfl
  · exact absurd (hE.trans _ _ _ hab h2) (by simp [h1])
  · exact absurd (hE.trans _ _ _ (hE.symm _ _ hab) h1) (by simp [h2])
  · rfl

@[simp] theorem lookup_nil (k : K) : lookup eq ([] : List (Option (K × V))) k = none := rfl
@[simp, ts_sym] theorem get?_empty (k : K) : ({} : JSMap K V).get? eq k = none := rfl
@[simp, ts_sym] theorem set_empty (k : K) (v : V) : ({} : JSMap K V).set eq k v = ⟨[some (k, v)]⟩ := rfl
@[simp] theorem lookup_none (l : List (Option (K × V))) (k : K) : lookup eq (none :: l) k = lookup eq l k := rfl
@[simp] theorem lookup_some (k' : K) (v : V) (l : List (Option (K × V))) (k : K) :
    lookup eq (some (k', v) :: l) k = if eq k' k then some v else lookup eq l k := rfl

theorem lookup_append (l₁ l₂ : List (Option (K × V))) (k : K) :
    lookup eq (l₁ ++ l₂) k = (lookup eq l₁ k).or (lookup eq l₂ k) := by
  induction l₁ with
  | nil => simp
  | cons e l ih =>
    rcases e with _ | ⟨k', v⟩
    · simpa using ih
    · simp only [List.cons_append, lookup_some]
      split <;> simp [ih]

theorem updAux_some (hE : Equiv eq) (k : K) (v : V) :
    ∀ (l l' : List (Option (K × V))), updAux eq k v l = some l' →
      ∀ k', lookup eq l' k' = if eq k k' then some v else lookup eq l k' := by
  intro l
  induction l with
  | nil => intro l' h; simp [updAux] at h
  | cons e l ih =>
    intro l' h k'
    rcases e with _ | ⟨k₁, v₁⟩
    · simp only [updAux, Option.map_eq_some_iff] at h
      obtain ⟨l'', h1, rfl⟩ := h
      simpa using ih l'' h1 k'
    · simp only [updAux] at h
      by_cases hk : eq k₁ k = true
      · simp only [hk, ite_true, Option.some.injEq] at h
        subst h
        rw [lookup_some, lookup_some, hE.congr_left hk]
        split <;> simp_all
      · simp only [hk, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨l'', h1, rfl⟩ := h
        rw [lookup_some, lookup_some, ih l'' h1 k']
        by_cases hk' : eq k₁ k' = true
        · have : eq k k' = false := by
            cases h3 : eq k k' with
            | false => rfl
            | true => exact absurd (hE.trans _ _ _ hk' (hE.symm _ _ h3)) hk
          simp [hk', this]
        · simp [hk']

theorem updAux_none (hE : Equiv eq) (k : K) (v : V) :
    ∀ (l : List (Option (K × V))), updAux eq k v l = none →
      ∀ k', eq k k' = true → lookup eq l k' = none := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons e l ih =>
    intro h k' hkk'
    rcases e with _ | ⟨k₁, v₁⟩
    · simp only [updAux, Option.map_eq_none_iff] at h
      simpa using ih h k' hkk'
    · simp only [updAux] at h
      by_cases hk : eq k₁ k = true
      · simp [hk] at h
      · simp only [hk, Bool.false_eq_true, ite_false, Option.map_eq_none_iff] at h
        have : eq k₁ k' = false := by
          cases h3 : eq k₁ k' with
          | false => rfl
          | true => exact absurd (hE.trans _ _ _ h3 (hE.symm _ _ hkk')) hk
        simp [this, ih h k' hkk']

/-- Looking up after `set`: the new value for keys equal to `k`, the old lookup otherwise. -/
theorem get?_set (hE : Equiv eq) (m : JSMap K V) (k k' : K) (v : V) :
    (m.set eq k v).get? eq k' = if eq k k' then some v else m.get? eq k' := by
  unfold set get?
  split
  · next l h => exact updAux_some hE k v _ _ h k'
  · next h =>
    simp only [lookup_append, lookup_some, lookup_nil]
    by_cases hk : eq k k' = true
    · simp [hk, updAux_none hE k v _ h k' hk]
    · cases hl : lookup eq m.entries k' <;> simp_all

theorem lookup_delAll (hE : Equiv eq) (k : K) :
    ∀ (l : List (Option (K × V))) (k' : K),
      lookup eq (delAll eq k l).1 k' = if eq k k' then none else lookup eq l k' := by
  intro l
  induction l with
  | nil => intro k'; simp [delAll]
  | cons e l ih =>
    intro k'
    rcases e with _ | ⟨k₁, v₁⟩
    · simp [delAll, ih]
    · simp only [delAll]
      by_cases hk : eq k₁ k = true
      · simp only [hk, ite_true, lookup_none, lookup_some, ih, hE.congr_left hk]
        split <;> rfl
      · simp only [hk, Bool.false_eq_true, ite_false, lookup_some, ih]
        by_cases hk' : eq k₁ k' = true
        · have : eq k k' = false := by
            cases h3 : eq k k' with
            | false => rfl
            | true => exact absurd (hE.trans _ _ _ hk' (hE.symm _ _ h3)) hk
          simp [hk', this]
        · simp [hk']

/-- Looking up after `delete`. -/
theorem get?_delete (hE : Equiv eq) (m : JSMap K V) (k k' : K) :
    (m.delete eq k).1.get? eq k' = if eq k k' then none else m.get? eq k' :=
  lookup_delAll hE k m.entries k'

theorem has_eq (m : JSMap K V) (k : K) : m.has eq k = (m.get? eq k).isSome := rfl

/-- Equality of `Decidable` values is an equivalence (keys compared by `==`). -/
theorem equiv_beq {α : Type} [DecidableEq α] : Equiv (fun (a b : α) => decide (a = b)) :=
  ⟨by simp, by intro a b h; simp_all, by intro a b c h1 h2; simp_all⟩

end JSMap
end StrictTS
