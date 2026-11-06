/-!
# Patch certificates (language independent)

A patch replaces an original program `old` by `new`. veriforch accepts it only with two theorems:

* `new_safe`: the new program is safe on every input satisfying the contract's precondition `Pre`;
* `conservative`: wherever the original program is safe, the new one has the same outcome.

Then, on every input satisfying `Pre`, the outcome changed exactly when the original was unsafe:
the patch fixes every failing input and touches nothing else. A patch cannot obtain its proof by
changing behaviour on inputs where the original was already right.

Three forms: outcomes as `Option O` (`none` = unsafe) compared by equality, the same with an
outcome relation `R`, and an abstract form over predicates, which the bridge instantiations use
(e.g. cirlean with equiv-lean's `EquivOn`, where "same outcome" is `Equiv (ObsEq m)`).
-/

namespace VerifOrch

/-- Outcome form: `none` is an unsafe run (undefined behaviour, divergence, panic, ...). -/
theorem changed_iff_unsafe {X O : Type} (Pre : X → Prop) (old new : X → Option O)
    (new_safe : ∀ x, Pre x → (new x).isSome = true)
    (conservative : ∀ x, (old x).isSome = true → new x = old x) :
    ∀ x, Pre x → (new x ≠ old x ↔ old x = none) := by
  intro x hx
  constructor
  · intro hne
    cases ho : old x with
    | none => rfl
    | some o => exact absurd (conservative x (by simp [ho])) hne
  · intro ho heq
    have hs := new_safe x hx
    rw [heq, ho] at hs
    simp at hs

/-- Outcomes related by `R` (both runs safe and `R` holds); every other pair counts as changed. -/
def RelOut {O₁ O₂ : Type} (R : O₁ → O₂ → Prop) : Option O₁ → Option O₂ → Prop
  | some a, some b => R a b
  | _, _ => False

/-- Relational form: "unchanged" means the outcomes are related by `R`. On `Pre` the new run is
safe, and the outcomes stop being related exactly where the original run was unsafe. -/
theorem changed_iff_unsafe_rel {X O₁ O₂ : Type} (R : O₁ → O₂ → Prop) (Pre : X → Prop)
    (old : X → Option O₂) (new : X → Option O₁)
    (new_safe : ∀ x, Pre x → (new x).isSome = true)
    (conservative : ∀ x, (old x).isSome = true → RelOut R (new x) (old x)) :
    ∀ x, Pre x → (new x).isSome = true ∧ (¬ RelOut R (new x) (old x) ↔ old x = none) := by
  intro x hx
  refine ⟨new_safe x hx, ?_⟩
  constructor
  · intro hne
    cases ho : old x with
    | none => rfl
    | some o => exact absurd (conservative x (by simp [ho])) hne
  · intro ho hrel
    rw [ho] at hrel
    cases hn : new x <;> simp_all [RelOut]

/-- Abstract form. `Agree x`: the two runs on `x` have corresponding outcomes. `transfer`: if they
agree and the new run is safe, so is the original (true of every simulation in both directions). -/
theorem changed_iff_unsafe_of_agree {X : Type} (Pre SafeOld SafeNew Agree : X → Prop)
    (new_safe : ∀ x, Pre x → SafeNew x)
    (conservative : ∀ x, SafeOld x → Agree x)
    (transfer : ∀ x, Agree x → SafeNew x → SafeOld x) :
    ∀ x, Pre x → (¬ Agree x ↔ ¬ SafeOld x) := by
  intro x hx
  exact ⟨fun hna hs => hna (conservative x hs), fun hns ha => hns (transfer x ha (new_safe x hx))⟩

/-- The changed set, as a set: on `Pre`, it is exactly the set of inputs where the original fails. -/
theorem changed_set_eq {X : Type} (Pre SafeOld SafeNew Agree : X → Prop)
    (new_safe : ∀ x, Pre x → SafeNew x)
    (conservative : ∀ x, SafeOld x → Agree x)
    (transfer : ∀ x, Agree x → SafeNew x → SafeOld x) :
    (fun x => Pre x ∧ ¬ Agree x) = (fun x => Pre x ∧ ¬ SafeOld x) := by
  funext x
  apply propext
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, (changed_iff_unsafe_of_agree Pre SafeOld SafeNew Agree new_safe conservative transfer x hp).1 h⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, (changed_iff_unsafe_of_agree Pre SafeOld SafeNew Agree new_safe conservative transfer x hp).2 h⟩

end VerifOrch
