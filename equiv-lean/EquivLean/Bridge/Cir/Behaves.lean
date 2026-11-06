import CIR
import EquivLean.Core.Sim

/-!
# cirlean bridge: outcome semantics of `CIR.Res`

cirlean gives a C++ function `f` the meaning `CIR.evalCall ctx f.sym args m : Res (Exit × Mem)`,
defined by `partial_fixpoint` in the flat order with bottom `Res.div`.  The outcome semantics
used by equiv-lean:

* `Runs x a :↔ x = .ok a`: the observable outcome of a call is the pair of its `Exit`
  (`.ret v` or an escaping exception `.exn x`, both observable) and the final memory;
* `Safe x :↔ ∃ a, x = .ok a`: undefined behaviour (`Res.ub`: signed overflow, invalid memory
  access, read of an indeterminate value, unsupported operation, ...) and divergence
  (`Res.div`) are unsafe.

The instance is total (`Safe` includes termination) and deterministic, so `wp x Q` is
cirlean's total-correctness judgement `x.holds Q` (`wp_res`), and a simulation against a CIR
source is a statement about its unique `ok` outcome (`sim_res_iff`).
-/

namespace EquivLean.Cir

open CIR

instance instBehavesRes (α : Type) : Behaves (Res α) α where
  Runs x a := x = .ok a
  Safe x := ∃ a, x = .ok a

instance (α : Type) : Behaves.Total (Res α) := ⟨fun _ h => h⟩
instance (α : Type) : Behaves.Det (Res α) :=
  ⟨fun _ _ _ h₁ h₂ => by cases h₁; cases h₂; rfl⟩

section
variable {α β : Type}

@[simp] theorem runs_res (x : Res α) (a : α) : Runs x a ↔ x = .ok a := Iff.rfl
@[simp] theorem safe_res (x : Res α) : Safe x ↔ ∃ a, x = .ok a := Iff.rfl

theorem safe_res_iff_holds (x : Res α) : Safe x ↔ x.holds (fun _ => True) := by
  cases x <;> simp [Res.holds]

/-- The weakest precondition of a CIR computation is cirlean's total correctness. -/
@[simp] theorem wp_res (x : Res α) (Q : α → Prop) : wp x Q ↔ x.holds Q := by
  cases x <;> simp [wp, Res.holds]

theorem holds_of_wp {x : Res α} {Q : α → Prop} (h : wp x Q) : x.holds Q := (wp_res x Q).1 h
theorem wp_of_holds {x : Res α} {Q : α → Prop} (h : x.holds Q) : wp x Q := (wp_res x Q).2 h

/-! ### Simulation against a CIR source

A CIR source has at most one outcome and is unsafe otherwise, so the source side of `Sim`
reduces to "if the source runs to `os`".  Three equivalent forms: an equation, the source's
total correctness for the postcondition `(· = os)` (the form the tactic executes in a
hypothesis), and partial correctness. -/

/-- Partial correctness: every `ok` result satisfies `K` (UB and divergence satisfy
everything). -/
def pholds (x : Res α) (K : α → Prop) : Prop := ∀ a, x = .ok a → K a

@[simp] theorem pholds_ok {a : α} {K : α → Prop} : pholds (.ok a) K ↔ K a :=
  ⟨fun h => h a rfl, fun h _ e => by cases e; exact h⟩
@[simp] theorem pholds_ub {m : String} {K : α → Prop} : pholds (.ub m) K ↔ True :=
  ⟨fun _ => trivial, fun _ _ e => by cases e⟩
@[simp] theorem pholds_div {K : α → Prop} : pholds .div K ↔ True :=
  ⟨fun _ => trivial, fun _ _ e => by cases e⟩
@[simp] theorem pholds_pure {a : α} {K : α → Prop} : pholds (pure a) K ↔ K a := pholds_ok
@[simp] theorem pholds_bind {x : Res α} {f : α → Res β} {K : β → Prop} :
    pholds (x >>= f) K ↔ pholds x (fun a => pholds (f a) K) := by
  cases x <;> simp [pholds, Res.ok_bind, Res.ub_bind, Res.div_bind]

theorem pholds_of_holds {x : Res α} {K : α → Prop} (h : x.holds K) : pholds x K := by
  cases x <;> simp_all [Res.holds]

/-- Simulation of a CIR source: the target is checked against the source's outcome. -/
theorem sim_res_iff {OT : Type} {T : Type} [Behaves T OT] {R : OT → α → Prop} {t : T}
    {s : Res α} : Sim R t s ↔ ∀ os, s = .ok os → wp t (fun ot => R ot os) := by
  constructor
  · intro h os hs
    exact (sim_iff_of_runs (R := R) (t := t) ((safe_res s).2 ⟨os, hs⟩) hs).1 h
  · intro h hsafe
    obtain ⟨os, hs⟩ := (safe_res s).1 hsafe
    exact (sim_iff_of_runs (R := R) (t := t) hsafe hs).2 (h os hs) hsafe

/-- `sim_res_iff` with the source as a total-correctness hypothesis: symbolic execution of
`hs : s.holds (· = os)` ends in an equation for `os`. -/
theorem sim_res_iff_holds {OT : Type} {T : Type} [Behaves T OT] {R : OT → α → Prop} {t : T}
    {s : Res α} : Sim R t s ↔ ∀ os, s.holds (fun a => a = os) → wp t (fun ot => R ot os) := by
  rw [sim_res_iff]
  refine forall_congr' fun os => imp_congr_left ?_
  cases s <;> simp [Res.holds, eq_comm]

/-- `sim_res_iff` as partial correctness of the source. -/
theorem sim_res_iff_pholds {OT : Type} {T : Type} [Behaves T OT] {R : OT → α → Prop} {t : T}
    {s : Res α} : Sim R t s ↔ pholds s (fun os => wp t (fun ot => R ot os)) :=
  sim_res_iff

/-- Two CIR computations: the target's total correctness under the source's outcome. -/
theorem sim_res_res {R : β → α → Prop} {t : Res β} {s : Res α} :
    Sim R t s ↔ ∀ os, s.holds (fun a => a = os) → t.holds (fun ot => R ot os) := by
  rw [sim_res_iff_holds]; simp only [wp_res]

end

end EquivLean.Cir
