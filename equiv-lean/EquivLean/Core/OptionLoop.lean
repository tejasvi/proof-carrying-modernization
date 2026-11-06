import EquivLean.Core.Loop

/-!
# A reference loop for plain Lean programs

`optLoop body s` iterates a state-passing body in the `Option` monad (`none` = divergence or
failure) until it returns `.inl b`.  It is the loop of the "local-state transformer" end of
the bridge: a reference implementation or a specification written as a Lean loop compares
with any encoding's loop through the product rules of `EquivLean.Core.Loop`.

The file also shows the two facts every bridge proves for its own loops, on the smallest
example:

* `LoopShape`: from the unfolding equation of the `partial_fixpoint` definition;
* `LoopShape.Terminates`: by fixpoint induction.  In a flat order a predicate that holds at
  bottom is admissible (`Lean.Order.admissible_flatOrder`), and "if `f s` is defined then the
  iteration from `s` is well-founded" holds at bottom vacuously.
-/

namespace EquivLean

universe u v

variable {σ : Type u} {β : Type v}

/-- Iterate `body` from `s` until it returns `.inl b`. -/
def optLoop (body : σ → Option (β ⊕ σ)) (s : σ) : Option β :=
  match body s with
  | none => none
  | some (.inl b) => some b
  | some (.inr s') => optLoop body s'
partial_fixpoint

theorem optLoop_unfold (body : σ → Option (β ⊕ σ)) (s : σ) :
    optLoop body s = match body s with
      | none => none
      | some (.inl b) => some b
      | some (.inr s') => optLoop body s' := by
  rw [optLoop]

theorem optLoop_shape (body : σ → Option (β ⊕ σ)) :
    LoopShape (optLoop body) body id := by
  constructor
  · intro s
    rw [optLoop_unfold]
    constructor
    · intro h
      split at h
      · exact absurd h (by simp [Safe, Behaves.Safe])
      · next b hb =>
        refine ⟨by simp [Safe, Behaves.Safe, hb], fun r s' hr hc => ?_⟩
        simp only [Runs, Behaves.Runs, hb, Option.some.injEq] at hr
        subst hr; simp at hc
      · next s₁ hb =>
        refine ⟨by simp [Safe, Behaves.Safe, hb], fun r s' hr hc => ?_⟩
        simp only [Runs, Behaves.Runs, hb, Option.some.injEq] at hr
        subst hr; simp only [id, Sum.inr.injEq] at hc; subst hc; exact h
    · rintro ⟨h₁, h₂⟩
      cases hb : body s with
      | none => simp [Safe, Behaves.Safe, hb] at h₁
      | some r =>
        cases r with
        | inl b => simp [Safe, Behaves.Safe]
        | inr s' => exact h₂ (.inr s') s' hb rfl
  · intro s o
    rw [optLoop_unfold]
    simp only [Runs, Behaves.Runs, id]
    constructor
    · intro h
      split at h
      · exact absurd h (by simp)
      · next b hb => exact ⟨.inl b, hb, .inl (by simpa using h)⟩
      · next s₁ hb => exact ⟨.inr s₁, hb, .inr ⟨s₁, rfl, h⟩⟩
    · rintro ⟨r, hr, h⟩
      rw [hr]
      rcases h with h | ⟨s', h, ho⟩
      · subst h; rfl
      · subst h; exact ho

theorem optLoop_terminates (body : σ → Option (β ⊕ σ)) :
    LoopShape.Terminates (optLoop body) body id := by
  intro s hs
  -- fixpoint induction: every defined approximation of the loop iterates finitely often
  have key : ∀ s, (optLoop body s).isSome → Acc (LoopShape.Next body id) s := by
    refine optLoop.fixpoint_induct body
      (motive := fun f => ∀ s, (f s).isSome → Acc (LoopShape.Next body id) s) ?adm ?step
    case adm =>
      apply Lean.Order.admissible_pi_apply
        (P := fun s (y : Option β) => y.isSome = true → Acc (LoopShape.Next body id) s)
      intro s
      exact Lean.Order.admissible_flatOrder _ (by intro h; simp [Lean.Order.FlatOrder.mk] at h)
    case step =>
      intro f ih s h
      refine Acc.intro s fun s' ⟨r, hr, hc⟩ => ?_
      simp only [Runs, Behaves.Runs, id] at hr hc
      subst hc
      simp only [hr] at h
      exact ih s' h
  exact key s hs

end EquivLean
