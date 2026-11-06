import EquivLean.Core.Sim

/-!
# Loops as product programs

Every encoding executes a structured loop the same way: one iteration, then either leave the
loop or start the next iteration from a new state.

    L s  =  iter s >>= fun r => match cls r with
              | .inl o  => (leave with outcome o)      -- condition false, break, return, throw
              | .inr s' => L s'                        -- next iteration

`LoopShape L iter cls` records this unfolding at the level of outcomes, so that the loop rules
below hold for every encoding at once.  A bridge proves `LoopShape` once per loop construct
(`cir.for`, `while`, `PERFORM … UNTIL`, Aeneas' `loop`, …).

The relational rules pair two loops into one product loop:

* `sim_loop`: lockstep with a coupling invariant and a variant;
* `sim_loop_of_terminates`: lockstep with a coupling invariant only.  Termination comes from
  the source: a safe source loop iterates finitely often (`LoopShape.Terminates`), and in
  lockstep the target performs the same number of iterations;
* `sim_loop_stutter`: asynchronous alignment.  A scheduler decides per product state whether
  both loops iterate, or only one of them; this covers unrolled, split and peeled loops;
* `wp_loop`: the one-sided rule, for a loop compared with a closed form.

Early exits need no special treatment: an iteration that leaves the loop (`.inl`) on one side
must leave it on the other side too, with related outcomes, which is exactly what a
`break`/`return`/exception refactoring has to preserve.
-/

namespace EquivLean

universe uC uD vO vD w

section
variable {σ : Type w} {C : Type uC} {D : Type uD} {O : Type vO} {OD : Type vD}
variable [Behaves C O] [Behaves D OD]

/-- `L` unfolds into one iteration `iter` followed by the classification `cls` of its outcome:
`.inl o` leaves the loop with the loop outcome `o`, `.inr s'` continues from `s'`. -/
structure LoopShape (L : σ → C) (iter : σ → D) (cls : OD → O ⊕ σ) : Prop where
  safe_iff : ∀ s, Safe (L s) ↔
    Safe (iter s) ∧ ∀ r s', Runs (iter s) r → cls r = .inr s' → Safe (L s')
  runs_iff : ∀ s o, Runs (L s) o ↔
    ∃ r, Runs (iter s) r ∧ (cls r = .inl o ∨ ∃ s', cls r = .inr s' ∧ Runs (L s') o)

/-- One iteration continues from `s'`. -/
def LoopShape.Next (iter : σ → D) (cls : OD → O ⊕ σ) (s' s : σ) : Prop :=
  ∃ r, Runs (iter s) r ∧ cls r = .inr s'

/-- Safe runs of the loop iterate finitely often.  Bridges prove it from the fixpoint
definition of the loop (or from fuel), so loop proofs need no variant. -/
def LoopShape.Terminates (L : σ → C) (iter : σ → D) (cls : OD → O ⊕ σ) : Prop :=
  ∀ s, Safe (L s) → Acc (LoopShape.Next iter cls) s

namespace LoopShape
variable {L : σ → C} {iter : σ → D} {cls : OD → O ⊕ σ}

theorem safe_iter (h : LoopShape L iter cls) {s : σ} (hs : Safe (L s)) : Safe (iter s) :=
  ((h.safe_iff s).1 hs).1

theorem safe_next (h : LoopShape L iter cls) {s s' : σ} {r : OD} (hs : Safe (L s))
    (hr : Runs (iter s) r) (hc : cls r = .inr s') : Safe (L s') :=
  ((h.safe_iff s).1 hs).2 r s' hr hc

theorem runs_exit (h : LoopShape L iter cls) {s : σ} {r : OD} {o : O}
    (hr : Runs (iter s) r) (hc : cls r = .inl o) : Runs (L s) o :=
  (h.runs_iff s o).2 ⟨r, hr, .inl hc⟩

theorem runs_next (h : LoopShape L iter cls) {s s' : σ} {r : OD} {o : O}
    (hr : Runs (iter s) r) (hc : cls r = .inr s') (ho : Runs (L s') o) : Runs (L s) o :=
  (h.runs_iff s o).2 ⟨r, hr, .inr ⟨s', hc, ho⟩⟩

/-- Unfolding the weakest precondition of a loop by one iteration. -/
theorem wp_unfold (h : LoopShape L iter cls) (s : σ) (Q : O → Prop) :
    wp (L s) Q ↔ wp (iter s) (fun r => match cls r with
      | .inl o => Q o
      | .inr s' => wp (L s') Q) := by
  constructor
  · intro hw
    refine ⟨h.safe_iter hw.1, fun r hr => ?_⟩
    dsimp only
    split
    · next o hc => exact hw.2 o (h.runs_exit hr hc)
    · next s' hc => exact ⟨h.safe_next hw.1 hr hc, fun o ho => hw.2 o (h.runs_next hr hc ho)⟩
  · intro hw
    refine ⟨(h.safe_iff s).2 ⟨hw.1, fun r s' hr hc => ?_⟩, fun o ho => ?_⟩
    · have := hw.2 r hr
      simp only [hc] at this
      exact this.1
    · obtain ⟨r, hr, hc⟩ := (h.runs_iff s o).1 ho
      have := hw.2 r hr
      rcases hc with hc | ⟨s', hc, ho'⟩
      · simp only [hc] at this; exact this
      · simp only [hc] at this; exact this.2 o ho'

end LoopShape

/-- One-sided loop rule: invariant and variant. -/
theorem wp_loop {L : σ → C} {iter : σ → D} {cls : OD → O ⊕ σ} (h : LoopShape L iter cls)
    {Q : O → Prop} (Inv : σ → Prop) (V : σ → Nat)
    (hstep : ∀ s, Inv s → wp (iter s) (fun r => match cls r with
      | .inl o => Q o
      | .inr s' => Inv s' ∧ V s' < V s)) :
    ∀ s, Inv s → wp (L s) Q := by
  intro s
  induction hV : V s using Nat.strongRecOn generalizing s with
  | ind n ih =>
    intro hinv
    rw [h.wp_unfold]
    refine wp_mono (hstep s hinv) fun r hr => ?_
    split
    · next o hc => simp only [hc] at hr; exact hr
    · next s' hc =>
      simp only [hc] at hr
      exact ih (V s') (hV ▸ hr.2) s' rfl hr.1

end

/-! ## Lockstep product of two loops -/

section
variable {σ₁ : Type w} {σ₂ : Type w} {C₁ D₁ C₂ D₂ : Type uC} {O₁ OD₁ O₂ OD₂ : Type vO}
variable [Behaves C₁ O₁] [Behaves D₁ OD₁] [Behaves C₂ O₂] [Behaves D₂ OD₂]

/-- The relation one lockstep iteration must establish: both sides leave the loop with
related outcomes, or both continue with states related by `J`. -/
def StepRel (cls₁ : OD₁ → O₁ ⊕ σ₁) (cls₂ : OD₂ → O₂ ⊕ σ₂) (R : O₁ → O₂ → Prop)
    (J : σ₁ → σ₂ → Prop) (r₁ : OD₁) (r₂ : OD₂) : Prop :=
  match cls₁ r₁, cls₂ r₂ with
  | .inl o₁, .inl o₂ => R o₁ o₂
  | .inr s₁, .inr s₂ => J s₁ s₂
  | _, _ => False

theorem stepRel_def (cls₁ : OD₁ → O₁ ⊕ σ₁) (cls₂ : OD₂ → O₂ ⊕ σ₂) (R : O₁ → O₂ → Prop)
    (J : σ₁ → σ₂ → Prop) (r₁ : OD₁) (r₂ : OD₂) :
    StepRel cls₁ cls₂ R J r₁ r₂ = match cls₁ r₁, cls₂ r₂ with
      | .inl o₁, .inl o₂ => R o₁ o₂
      | .inr s₁, .inr s₂ => J s₁ s₂
      | _, _ => False := rfl

variable {L₁ : σ₁ → C₁} {iter₁ : σ₁ → D₁} {cls₁ : OD₁ → O₁ ⊕ σ₁}
variable {L₂ : σ₂ → C₂} {iter₂ : σ₂ → D₂} {cls₂ : OD₂ → O₂ ⊕ σ₂}

/-- The core of both lockstep rules: one product iteration, with the hypothesis for the
next iteration given by `ih`. -/
private theorem sim_loop_step (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} {J : σ₁ → σ₂ → Prop} {s₁ : σ₁} {s₂ : σ₂}
    (hstep : Sim (StepRel cls₁ cls₂ R J) (iter₁ s₁) (iter₂ s₂))
    (ih : ∀ s₁' s₂', J s₁' s₂' → LoopShape.Next iter₂ cls₂ s₂' s₂ →
      Sim R (L₁ s₁') (L₂ s₂')) :
    Sim R (L₁ s₁) (L₂ s₂) := by
  intro hs₂
  obtain ⟨hi₁, pair⟩ := hstep (h₂.safe_iter hs₂)
  refine ⟨(h₁.safe_iff s₁).2 ⟨hi₁, fun r₁ s₁' hr₁ hc₁ => ?_⟩, fun o₁ ho₁ => ?_⟩
  · obtain ⟨r₂, hr₂, hrel⟩ := pair r₁ hr₁
    unfold StepRel at hrel
    rw [hc₁] at hrel
    cases hc₂ : cls₂ r₂ with
    | inl o₂ => rw [hc₂] at hrel; exact False.elim hrel
    | inr s₂' =>
      rw [hc₂] at hrel
      exact (ih s₁' s₂' hrel ⟨r₂, hr₂, hc₂⟩ (h₂.safe_next hs₂ hr₂ hc₂)).1
  · obtain ⟨r₁, hr₁, hc₁⟩ := (h₁.runs_iff s₁ o₁).1 ho₁
    obtain ⟨r₂, hr₂, hrel⟩ := pair r₁ hr₁
    unfold StepRel at hrel
    rcases hc₁ with hc₁ | ⟨s₁', hc₁, ho₁'⟩
    · rw [hc₁] at hrel
      cases hc₂ : cls₂ r₂ with
      | inl o₂ => rw [hc₂] at hrel; exact ⟨o₂, h₂.runs_exit hr₂ hc₂, hrel⟩
      | inr s₂' => rw [hc₂] at hrel; exact False.elim hrel
    · rw [hc₁] at hrel
      cases hc₂ : cls₂ r₂ with
      | inl o₂ => rw [hc₂] at hrel; exact False.elim hrel
      | inr s₂' =>
        rw [hc₂] at hrel
        obtain ⟨_, hrun'⟩ := ih s₁' s₂' hrel ⟨r₂, hr₂, hc₂⟩ (h₂.safe_next hs₂ hr₂ hc₂)
        obtain ⟨o₂, ho₂, hR⟩ := hrun' o₁ ho₁'
        exact ⟨o₂, h₂.runs_next hr₂ hc₂ ho₂, hR⟩

/-- **Lockstep loops, with a variant.**  If the coupling invariant `I` is preserved by one
iteration of each loop (or both loops leave with related outcomes) and `V` decreases, the
two loops simulate each other from every coupled pair of states. -/
theorem sim_loop (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} (I : σ₁ → σ₂ → Prop) (V : σ₁ → σ₂ → Nat)
    (hstep : ∀ s₁ s₂, I s₁ s₂ → Sim (StepRel cls₁ cls₂ R
      (fun s₁' s₂' => I s₁' s₂' ∧ V s₁' s₂' < V s₁ s₂)) (iter₁ s₁) (iter₂ s₂)) :
    ∀ s₁ s₂, I s₁ s₂ → Sim R (L₁ s₁) (L₂ s₂) := by
  intro s₁ s₂
  induction hV : V s₁ s₂ using Nat.strongRecOn generalizing s₁ s₂ with
  | ind n ih =>
    intro hI
    exact sim_loop_step h₁ h₂ (hstep s₁ s₂ hI) fun s₁' s₂' ⟨hI', hlt⟩ _ =>
      ih (V s₁' s₂') (hV ▸ hlt) s₁' s₂' rfl hI'

/-- **Lockstep loops, no variant.**  When the source loop terminates whenever it is safe
(`LoopShape.Terminates`, proved once per loop construct by each bridge), the coupling
invariant alone suffices: the target performs as many iterations as the source. -/
theorem sim_loop_of_terminates (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    (ht : LoopShape.Terminates L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} (I : σ₁ → σ₂ → Prop)
    (hstep : ∀ s₁ s₂, I s₁ s₂ → Sim (StepRel cls₁ cls₂ R I) (iter₁ s₁) (iter₂ s₂)) :
    ∀ s₁ s₂, I s₁ s₂ → Sim R (L₁ s₁) (L₂ s₂) := by
  intro s₁ s₂ hI hs₂
  have hacc := ht s₂ hs₂
  revert s₁ hs₂
  induction hacc with
  | intro s₂ _ ih =>
    intro s₁ hI hs₂
    exact sim_loop_step h₁ h₂ (hstep s₁ s₂ hI)
      (fun s₁' s₂' hI' hnext hs₂' => ih s₂' hnext s₁' hI' hs₂') hs₂

/-- The pair of lockstep rules in hypothesis form, as used by the tactics: the source loop
is the head of a hypothesis `wp (L₂ s₂) K₂`, the target loop the head of the goal. -/
theorem wp_loop_rel (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    (ht : LoopShape.Terminates L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} (I : σ₁ → σ₂ → Prop) {s₁ : σ₁} {s₂ : σ₂}
    {K₁ : O₁ → Prop} {K₂ : O₂ → Prop}
    (hs : wp (L₂ s₂) K₂) (hI : I s₁ s₂)
    (hstep : ∀ s₁ s₂, I s₁ s₂ → Sim (StepRel cls₁ cls₂ R I) (iter₁ s₁) (iter₂ s₂))
    (hk : ∀ o₁ o₂, R o₁ o₂ → K₂ o₂ → K₁ o₁) : wp (L₁ s₁) K₁ :=
  (sim_loop_of_terminates h₁ h₂ ht I hstep s₁ s₂ hI).wp_cut hs hk

end

/-! ## Asynchronous product (stuttering)

Loops whose iterations do not correspond one to one (unrolling, loop splitting, peeling,
strip-mining) are aligned by a scheduler: in each product state, either both loops iterate,
or only the target, or only the source.  A single variant decreases on every product step. -/

/-- Which loops advance in a product step. -/
inductive Sched where
  | both
  | left   -- only the target iterates
  | right  -- only the source iterates
  deriving DecidableEq, Repr

section
variable {σ₁ : Type w} {σ₂ : Type w} {C₁ D₁ C₂ D₂ : Type uC} {O₁ OD₁ O₂ OD₂ : Type vO}
variable [Behaves C₁ O₁] [Behaves D₁ OD₁] [Behaves C₂ O₂] [Behaves D₂ OD₂]
variable {L₁ : σ₁ → C₁} {iter₁ : σ₁ → D₁} {cls₁ : OD₁ → O₁ ⊕ σ₁}
variable {L₂ : σ₂ → C₂} {iter₂ : σ₂ → D₂} {cls₂ : OD₂ → O₂ ⊕ σ₂}

/-- **Stuttering loops.**  `sched s₁ s₂` picks the kind of product step.
* `both`: as in lockstep;
* `left`: one target iteration that stays in the loop (`.inr`) and keeps `I` with the
  source state unchanged;
* `right`: one source iteration that stays in the loop and keeps `I` with the target state
  unchanged (stated as a weakest precondition of the source).
The source must be total for `right` steps to be matched (`Behaves.Total D₂`). -/
theorem sim_loop_stutter [Behaves.Total D₂]
    (h₁ : LoopShape L₁ iter₁ cls₁) (h₂ : LoopShape L₂ iter₂ cls₂)
    {R : O₁ → O₂ → Prop} (I : σ₁ → σ₂ → Prop) (V : σ₁ → σ₂ → Nat) (sched : σ₁ → σ₂ → Sched)
    (hboth : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .both → Sim (StepRel cls₁ cls₂ R
      (fun s₁' s₂' => I s₁' s₂' ∧ V s₁' s₂' < V s₁ s₂)) (iter₁ s₁) (iter₂ s₂))
    (hleft : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .left → wp (iter₁ s₁) (fun r₁ =>
      ∃ s₁', cls₁ r₁ = .inr s₁' ∧ I s₁' s₂ ∧ V s₁' s₂ < V s₁ s₂))
    (hright : ∀ s₁ s₂, I s₁ s₂ → sched s₁ s₂ = .right → Safe (iter₂ s₂) → wp (iter₂ s₂) (fun r₂ =>
      ∃ s₂', cls₂ r₂ = .inr s₂' ∧ I s₁ s₂' ∧ V s₁ s₂' < V s₁ s₂)) :
    ∀ s₁ s₂, I s₁ s₂ → Sim R (L₁ s₁) (L₂ s₂) := by
  intro s₁ s₂
  induction hV : V s₁ s₂ using Nat.strongRecOn generalizing s₁ s₂ with
  | ind n ih =>
    intro hI
    cases hsch : sched s₁ s₂ with
    | both =>
      exact sim_loop_step h₁ h₂ (hboth s₁ s₂ hI hsch) fun s₁' s₂' ⟨hI', hlt⟩ _ =>
        ih (V s₁' s₂') (hV ▸ hlt) s₁' s₂' rfl hI'
    | left =>
      intro hs₂
      have hl := hleft s₁ s₂ hI hsch
      refine ⟨(h₁.safe_iff s₁).2 ⟨hl.1, fun r₁ s₁' hr₁ hc₁ => ?_⟩, fun o₁ ho₁ => ?_⟩
      · obtain ⟨s₁'', hc, hI', hlt⟩ := hl.2 r₁ hr₁
        have he : s₁' = s₁'' := Sum.inr.inj (hc₁.symm.trans hc)
        subst he
        exact (ih _ (hV ▸ hlt) s₁' s₂ rfl hI' hs₂).1
      · obtain ⟨r₁, hr₁, hc₁⟩ := (h₁.runs_iff s₁ o₁).1 ho₁
        obtain ⟨s₁'', hc, hI', hlt⟩ := hl.2 r₁ hr₁
        rcases hc₁ with hc₁ | ⟨s₁', hc₁, ho₁'⟩
        · exact absurd (hc₁.symm.trans hc) (by simp)
        · have he : s₁' = s₁'' := Sum.inr.inj (hc₁.symm.trans hc)
          subst he
          exact (ih _ (hV ▸ hlt) s₁' s₂ rfl hI' hs₂).2 o₁ ho₁'
    | right =>
      intro hs₂
      have hr := hright s₁ s₂ hI hsch (h₂.safe_iter hs₂)
      obtain ⟨r₂, hr₂, s₂', hc₂, hI', hlt⟩ := wp_exists hr
      have hs₂' := h₂.safe_next hs₂ hr₂ hc₂
      obtain ⟨hst, hrun⟩ := ih _ (hV ▸ hlt) s₁ s₂' rfl hI' hs₂'
      exact ⟨hst, fun o₁ ho₁ =>
        let ⟨o₂, ho₂, hR⟩ := hrun o₁ ho₁
        ⟨o₂, h₂.runs_next hr₂ hc₂ ho₂, hR⟩⟩

end

end EquivLean
