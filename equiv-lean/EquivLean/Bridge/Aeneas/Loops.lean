import EquivLean.Bridge.Aeneas.Behaves
import EquivLean.Core.Loop

/-!
# Aeneas (Rust) bridge: loops

Aeneas translates every Rust loop to its combinator `loop` (`partial_fixpoint`):

    @[rust_loop_body] def f_loop.body … (s : σ) : Result (ControlFlow σ β)
    @[rust_loop] def f_loop … := loop (fun s => f_loop.body … s) init

One iteration is the loop body.  Its outcome is classified by `loopCls`: `.ok (.cont s)` starts
the next iteration from `s`, `.ok (.done b)` leaves the loop with the result `b` (condition
false, `break`, `return`), and a panic `.error e` leaves the loop with that panic.

* `loop_shape`: `LoopShape (loop body) body loopCls`, so all loop rules of `Core/Loop.lean`
  apply to Aeneas loops;
* `loop_terminates`: `LoopShape.Terminates (loop body) body loopCls`: a loop that does not
  diverge iterates finitely often.  The proof is a fixpoint induction over Aeneas' order on
  `Result` (`loop.fixpoint_induct`), with admissibility from Aeneas' `dspec_admissible`.  So
  lockstep loop proofs (`sim_loop_of_terminates`, `wp_loop_rel`) need no variant when the
  source is an Aeneas loop.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

universe u v w

/-- Classification of the outcome of one iteration of `loop`. -/
def loopCls {α : Type u} {β : Type v} : Except Error (ControlFlow α β) → Except Error β ⊕ α
  | .ok (.cont s) => .inr s
  | .ok (.done b) => .inl (.ok b)
  | .error e => .inl (.error e)

section
variable {α : Type u} {β : Type v}

@[simp] theorem loopCls_cont (s : α) :
    loopCls (.ok (.cont s) : Except Error (ControlFlow α β)) = .inr s := rfl
@[simp] theorem loopCls_done (b : β) :
    loopCls (.ok (.done b) : Except Error (ControlFlow α β)) = .inl (.ok b) := rfl
@[simp] theorem loopCls_error (e : Error) :
    loopCls (.error e : Except Error (ControlFlow α β)) = .inl (.error e) := rfl

/-- One unfolding of `loop`. -/
theorem loop_unfold (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = Std.bind (body x) (fun r => match r with
      | .cont x => loop body x
      | .done b => Result.ok b) :=
  loop.eq_1 body x

/-- Aeneas' `loop` is a loop: one iteration is the body, classified by `loopCls`. -/
theorem loop_shape (body : α → Result (ControlFlow α β)) :
    LoopShape (loop body) body loopCls where
  safe_iff s := by
    rw [loop_unfold]
    rcases result_trichotomy (body s) with ⟨r, hr⟩ | ⟨e, hr⟩ | hr <;> rw [hr]
    · cases r with
      | cont s' =>
        simp only [safe_ok, runs_ok_iff, true_and, bind_ok]
        constructor
        · rintro h r s'' rfl hc
          simp only [loopCls_cont, Sum.inr.injEq] at hc
          exact hc ▸ h
        · intro h
          exact h _ s' rfl rfl
      | done b =>
        simp only [safe_ok, runs_ok_iff, true_and, bind_ok, true_iff]
        rintro r s' rfl hc
        simp at hc
    · simp only [bind_fail, safe_fail, runs_fail_iff, true_and, true_iff]
      rintro r s' rfl hc
      simp at hc
    · simp
  runs_iff s o := by
    rw [loop_unfold]
    rcases result_trichotomy (body s) with ⟨r, hr⟩ | ⟨e, hr⟩ | hr <;> rw [hr]
    · cases r with
      | cont s' => simp
      | done b => simp [eq_comm]
    · simp [eq_comm]
    · simp

/-- A loop that does not diverge iterates finitely often (fixpoint induction). -/
theorem loop_terminates (body : α → Result (ControlFlow α β)) :
    LoopShape.Terminates (loop body) body loopCls := by
  intro s hs
  have key : ∀ s, ¬ Acc (LoopShape.Next body loopCls) s → loop body s = Result.div := by
    refine loop.fixpoint_induct body
      (fun f => ∀ s, ¬ Acc (LoopShape.Next body loopCls) s → f s = Result.div) ?_ ?_
    · apply Lean.Order.admissible_pi
      intro s
      by_cases h : Acc (LoopShape.Next body loopCls) s
      · simp only [h, not_true_eq_false, false_implies]
        exact Lean.Order.admissible_const_true
      · simp only [h, not_false_eq_true, true_implies]
        have := WP.dspec_func_admissible (α := α) s (fun (_ : β) => False)
        simpa only [dspec_false_iff] using this
    · intro f ih s hs
      have : ∃ s', LoopShape.Next body loopCls s' s ∧ ¬ Acc (LoopShape.Next body loopCls) s' := by
        by_contra hne
        push Not at hne
        exact hs (Acc.intro s fun s' h => hne s' h)
      obtain ⟨s', ⟨r, hr, hc⟩, hs'⟩ := this
      have hbody : body s = Result.ok (.cont s') := by
        rcases r with e | (s'' | b)
        · simp at hc
        · simp only [loopCls_cont, Sum.inr.injEq] at hc
          subst hc
          exact runs_iff.1 hr
        · simp at hc
      show Std.bind (body s) _ = _
      rw [hbody, bind_ok]
      exact ih s' hs'
  exact Classical.byContradiction fun hacc => (safe_iff_ne_div.1 hs) (key s hacc)

end

/-! ## Lockstep equivalence of two Aeneas loops -/

section
variable {σ₁ σ₂ : Type u} {C₁ D₁ C₂ D₂ : Type v} {O₁ OD₁ O₂ OD₂ : Type w}
variable [Behaves C₁ O₁] [Behaves D₁ OD₁] [Behaves C₂ O₂] [Behaves D₂ OD₂]

theorem stepRel_symm (cls₁ : OD₁ → O₁ ⊕ σ₁) (cls₂ : OD₂ → O₂ ⊕ σ₂) (R : O₁ → O₂ → Prop)
    (J : σ₁ → σ₂ → Prop) (r₁ : OD₁) (r₂ : OD₂) :
    StepRel cls₁ cls₂ R J r₁ r₂ → StepRel cls₂ cls₁ (fun b a => R a b) (fun b a => J a b) r₂ r₁ := by
  simp only [stepRel_def]
  generalize cls₁ r₁ = a
  generalize cls₂ r₂ = b
  cases a <;> cases b <;> exact id

end

section
variable {σ₁ σ₂ β₁ β₂ : Type u}

/-- **Lockstep equivalence of two Aeneas loops.**  A coupling invariant `I` that one iteration
of each body preserves (or both leave the loop with related outcomes) gives equivalence of the
loops.  No variant: both loops terminate when safe (`loop_terminates`). -/
theorem equiv_loop {B₁ : σ₁ → Result (ControlFlow σ₁ β₁)} {B₂ : σ₂ → Result (ControlFlow σ₂ β₂)}
    {R : Except Error β₁ → Except Error β₂ → Prop} (I : σ₁ → σ₂ → Prop)
    (hstep : ∀ s₁ s₂, I s₁ s₂ → Equiv (StepRel loopCls loopCls R I) (B₁ s₁) (B₂ s₂)) :
    ∀ s₁ s₂, I s₁ s₂ → Equiv R (loop B₁ s₁) (loop B₂ s₂) := by
  intro s₁ s₂ hI
  refine ⟨sim_loop_of_terminates (loop_shape B₁) (loop_shape B₂) (loop_terminates B₂) I
    (fun a b h => (hstep a b h).1) s₁ s₂ hI, ?_⟩
  exact sim_loop_of_terminates (loop_shape B₂) (loop_shape B₁) (loop_terminates B₁)
    (fun b a => I a b)
    (fun b a h => (hstep a b h).2.mono fun r₂ r₁ hr => stepRel_symm _ _ _ _ r₁ r₂ hr) s₂ s₁ hI

/-- The one-directional version (the target may be any loop shape with the same outcome
type; here both are Aeneas loops). -/
theorem sim_loop' {B₁ : σ₁ → Result (ControlFlow σ₁ β₁)} {B₂ : σ₂ → Result (ControlFlow σ₂ β₂)}
    {R : Except Error β₁ → Except Error β₂ → Prop} (I : σ₁ → σ₂ → Prop)
    (hstep : ∀ s₁ s₂, I s₁ s₂ → Sim (StepRel loopCls loopCls R I) (B₁ s₁) (B₂ s₂)) :
    ∀ s₁ s₂, I s₁ s₂ → Sim R (loop B₁ s₁) (loop B₂ s₂) :=
  sim_loop_of_terminates (loop_shape B₁) (loop_shape B₂) (loop_terminates B₂) I hstep

end

end EquivLean.Aeneas
