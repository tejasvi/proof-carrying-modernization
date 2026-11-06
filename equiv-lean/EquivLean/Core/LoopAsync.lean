import EquivLean.Core.Loop

/-!
# Asynchronous loop pairing in hypothesis form

`sim_loop_stutter` (`EquivLean.Core.Loop`) aligns loops whose iterations do not correspond one
to one.  `wp_loop_stutter_rel` is the same rule in the form the tactics use: the source loop is
the head of a hypothesis `wp (L₂ s₂) K₂`, the target loop the head of the goal.
-/

namespace EquivLean

universe uC vO w

section
variable {σ₁ : Type w} {σ₂ : Type w} {C₁ D₁ C₂ D₂ : Type uC} {O₁ OD₁ O₂ OD₂ : Type vO}
variable [Behaves C₁ O₁] [Behaves D₁ OD₁] [Behaves C₂ O₂] [Behaves D₂ OD₂]
variable {L₁ : σ₁ → C₁} {iter₁ : σ₁ → D₁} {cls₁ : OD₁ → O₁ ⊕ σ₁}
variable {L₂ : σ₂ → C₂} {iter₂ : σ₂ → D₂} {cls₂ : OD₂ → O₂ ⊕ σ₂}

/-- Stuttering loops, hypothesis form.  See `sim_loop_stutter` for the three kinds of product
step chosen by `sched`. -/
theorem wp_loop_stutter_rel [Behaves.Total D₂]
    (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} (I : σ₁ → σ₂ → Prop) (V : σ₁ → σ₂ → Nat) (sched : σ₁ → σ₂ → Sched)
    {s₁ : σ₁} {s₂ : σ₂} {K₁ : O₁ → Prop} {K₂ : O₂ → Prop}
    (hs : wp (L₂ s₂) K₂) (hI : I s₁ s₂)
    (hboth : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .both → Sim (StepRel cls₁ cls₂ R
      (fun s₁' s₂' => I s₁' s₂' ∧ V s₁' s₂' < V s₁ s₂)) (iter₁ s₁) (iter₂ s₂))
    (hleft : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .left → wp (iter₁ s₁) (fun r₁ =>
      ∃ s₁', cls₁ r₁ = .inr s₁' ∧ I s₁' s₂ ∧ V s₁' s₂ < V s₁ s₂))
    (hright : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .right → Safe (iter₂ s₂) → wp (iter₂ s₂) (fun r₂ =>
      ∃ s₂', cls₂ r₂ = .inr s₂' ∧ I s₁ s₂' ∧ V s₁ s₂' < V s₁ s₂))
    (hk : ∀ o₁ o₂, R o₁ o₂ → K₂ o₂ → K₁ o₁) : wp (L₁ s₁) K₁ :=
  (sim_loop_stutter h₁ h₂ I V sched hboth hleft hright s₁ s₂ hI).wp_cut hs hk

end

end EquivLean
