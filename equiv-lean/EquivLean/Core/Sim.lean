import EquivLean.Core.Behaves

/-!
# Simulation and equivalence

`Sim R t s` is the central judgement: the *target* computation `t` simulates the *source*
computation `s` up to the outcome relation `R`.

    Sim R t s  :=  Safe s → Safe t ∧ ∀ ot, Runs t ot → ∃ os, Runs s os ∧ R ot os

Read it as: wherever the source cannot go wrong, the target cannot go wrong either, and every
outcome of the target is matched (up to `R`) by an outcome of the source.  With total
instances "cannot go wrong" includes termination, so for deterministic programs

    Sim R t s  ↔  (s terminates safely with o  →  t terminates safely with o' and R o' o).

`Equiv R t s` is simulation in both directions.  Inputs on which the source goes wrong carry
no obligation, so a precondition `¬ Bad x` is all that is needed to state "the patch changes
behaviour only where the old code was wrong":

    ∀ x, ¬ Bad x → Equiv R (f_new x) (f_old x)     -- ⇔  {x | f_new x ≉ f_old x} ⊆ Bad

The judgement lives between *any* two `Behaves` instances, so the same theorems and tactics
compare a Rust function with a COBOL program, two versions of a C++ function, or a Java
method with a pure Lean specification.

The typeclass `Simulates T S` packages the judgement for a pair of computation types, with
the outcome relation taken from the representation-refinement class `Corr` (see
`EquivLean.Repr.Corr`): `t ⊑ s` and `t ≈ s` then need no explicit relation.
-/

namespace EquivLean

universe u₁ u₂ u₃ v₁ v₂ v₃

section
variable {T : Type u₁} {S : Type u₂} {M : Type u₃} {OT : Type v₁} {OS : Type v₂} {OM : Type v₃}
variable [Behaves T OT] [Behaves S OS] [Behaves M OM]

/-- `t` simulates `s` up to the outcome relation `R` (backward simulation: the source's
safety is the hypothesis). -/
def Sim (R : OT → OS → Prop) (t : T) (s : S) : Prop :=
  Safe s → Safe t ∧ ∀ ot, Runs t ot → ∃ os, Runs s os ∧ R ot os

/-- Simulation in both directions: the same inputs are safe and the outcomes correspond. -/
def Equiv (R : OT → OS → Prop) (t : T) (s : S) : Prop :=
  Sim R t s ∧ Sim (fun os ot => R ot os) s t

@[inherit_doc] scoped notation:50 t " ⊑[" R "] " s => Sim R t s
@[inherit_doc] scoped notation:50 t " ≈[" R "] " s => Equiv R t s

/-- The weakest-precondition form of `Sim`, used by all tactics: run the source in a
hypothesis `wp s P` and the target in the goal. -/
theorem sim_iff_wp {R : OT → OS → Prop} {t : T} {s : S} :
    Sim R t s ↔ ∀ P : OS → Prop, wp s P → wp t (fun ot => ∃ os, P os ∧ R ot os) := by
  constructor
  · intro h P hs
    obtain ⟨hst, hrun⟩ := h hs.1
    exact ⟨hst, fun ot ho => let ⟨os, hos, hr⟩ := hrun ot ho; ⟨os, hs.2 os hos, hr⟩⟩
  · intro h hs
    exact h (Runs s) (wp_runs_self hs)

theorem Sim.intro_wp {R : OT → OS → Prop} {t : T} {s : S}
    (h : ∀ P : OS → Prop, wp s P → wp t (fun ot => ∃ os, P os ∧ R ot os)) : Sim R t s :=
  sim_iff_wp.2 h

/-- **Cut.**  Use a simulation between the next pieces of the two programs: if the source
continues with `K₂` and the target with `K₁`, it suffices that related outcomes pass from
`K₂` to `K₁`.  Every product-program step (aligned loops, calls with relational
specifications) is an instance of this rule. -/
theorem Sim.wp_cut {R : OT → OS → Prop} {t : T} {s : S} {K₁ : OT → Prop} {K₂ : OS → Prop}
    (hsim : Sim R t s) (hs : wp s K₂) (hk : ∀ ot os, R ot os → K₂ os → K₁ ot) : wp t K₁ := by
  obtain ⟨hst, hrun⟩ := hsim hs.1
  exact ⟨hst, fun ot ho => let ⟨os, hos, hr⟩ := hrun ot ho; hk ot os hr (hs.2 os hos)⟩

theorem Sim.mono {R R' : OT → OS → Prop} {t : T} {s : S} (h : Sim R t s)
    (hR : ∀ a b, R a b → R' a b) : Sim R' t s := fun hs =>
  let ⟨hst, hrun⟩ := h hs
  ⟨hst, fun ot ho => let ⟨os, hos, hr⟩ := hrun ot ho; ⟨os, hos, hR _ _ hr⟩⟩

theorem Sim.refl (c : T) : Sim (· = ·) c c := fun hs => ⟨hs, fun o ho => ⟨o, ho, rfl⟩⟩

/-- Simulations compose; the outcome relations compose relationally.  This is how a
migration is split into steps (COBOL → specification → Java), or two migrations are chained
through a common reference. -/
theorem Sim.trans {R₁ : OT → OM → Prop} {R₂ : OM → OS → Prop} {t : T} {m : M} {s : S}
    (h₁ : Sim R₁ t m) (h₂ : Sim R₂ m s) : Sim (fun ot os => ∃ om, R₁ ot om ∧ R₂ om os) t s :=
  fun hs =>
    let ⟨hms, hm⟩ := h₂ hs
    let ⟨hts, ht⟩ := h₁ hms
    ⟨hts, fun ot ho =>
      let ⟨om, hom, r₁⟩ := ht ot ho
      let ⟨os, hos, r₂⟩ := hm om hom
      ⟨os, hos, om, r₁, r₂⟩⟩

/-- A safe target that simulates its source turns the source's weakest precondition into the
target's. -/
theorem Sim.wp_transfer {R : OT → OS → Prop} {t : T} {s : S} {Q : OS → Prop}
    (h : Sim R t s) (hs : wp s Q) : wp t (fun ot => ∃ os, Q os ∧ R ot os) :=
  h.wp_cut hs (fun ot os hr hq => ⟨os, hq, hr⟩)

/-- Against a deterministic source with a known safe outcome, simulation is a weakest
precondition of the target alone. -/
theorem sim_iff_of_runs [Behaves.Det S] {R : OT → OS → Prop} {t : T} {s : S} {os : OS}
    (hs : Safe s) (hos : Runs s os) : Sim R t s ↔ wp t (fun ot => R ot os) := by
  constructor
  · intro h
    exact wp_mono (h.wp_transfer (wp_runs_self hs)) fun ot ⟨os', hos', hr⟩ =>
      (Behaves.Det.det s os os' hos hos') ▸ hr
  · intro h _
    exact ⟨h.1, fun ot ho => ⟨os, hos, h.2 ot ho⟩⟩

/-- A source with no safe run is simulated by anything. -/
theorem Sim.of_not_safe {R : OT → OS → Prop} {t : T} {s : S} (h : ¬ Safe s) : Sim R t s :=
  fun hs => absurd hs h

/-- Run the source to completion first, then the target ("self-composition").  Sound for
total sources; for deterministic sources it is also complete when the source is safe. -/
theorem Sim.of_seq [Behaves.Total S] {R : OT → OS → Prop} {t : T} {s : S}
    (h : wp s (fun os => wp t (fun ot => R ot os))) : Sim R t s := fun _ =>
  let ⟨os, hos, ht⟩ := wp_exists h
  ⟨ht.1, fun ot ho => ⟨os, hos, ht.2 ot ho⟩⟩

end

/-! ## Equivalence -/

section
variable {T : Type u₁} {S : Type u₂} {M : Type u₃} {OT : Type v₁} {OS : Type v₂} {OM : Type v₃}
variable [Behaves T OT] [Behaves S OS] [Behaves M OM]

theorem Equiv.sim {R : OT → OS → Prop} {t : T} {s : S} (h : Equiv R t s) : Sim R t s := h.1
theorem Equiv.sim_symm {R : OT → OS → Prop} {t : T} {s : S} (h : Equiv R t s) :
    Sim (fun os ot => R ot os) s t := h.2

theorem Equiv.symm {R : OT → OS → Prop} {t : T} {s : S} (h : Equiv R t s) :
    Equiv (fun os ot => R ot os) s t := ⟨h.2, h.1⟩

theorem Equiv.refl (c : T) : Equiv (· = ·) c c :=
  ⟨Sim.refl c, (Sim.refl c).mono fun _ _ h => h.symm⟩

theorem Equiv.trans {R₁ : OT → OM → Prop} {R₂ : OM → OS → Prop} {t : T} {m : M} {s : S}
    (h₁ : Equiv R₁ t m) (h₂ : Equiv R₂ m s) :
    Equiv (fun ot os => ∃ om, R₁ ot om ∧ R₂ om os) t s :=
  ⟨h₁.1.trans h₂.1, (h₂.2.trans h₁.2).mono fun _ _ ⟨om, r₂, r₁⟩ => ⟨om, r₁, r₂⟩⟩

theorem Equiv.mono {R R' : OT → OS → Prop} {t : T} {s : S} (h : Equiv R t s)
    (hR : ∀ a b, R a b → R' a b) : Equiv R' t s :=
  ⟨h.1.mono hR, h.2.mono fun a b => hR b a⟩

/-- Equivalent computations are safe on the same inputs. -/
theorem Equiv.safe_iff {R : OT → OS → Prop} {t : T} {s : S} (h : Equiv R t s) :
    Safe t ↔ Safe s :=
  ⟨fun ht => (h.2 ht).1, fun hs => (h.1 hs).1⟩

end

/-! ## Functions

`FSim Rin R f g`: related inputs give simulating computations.  This is the statement of a
whole-function equivalence, `∀ x, f_target x ≈ f_source x`, with representation relations
on both inputs and outputs. -/

section
universe w₁ w₂
variable {X : Type w₁} {Y : Type w₂} {T : Type u₁} {S : Type u₂} {OT : Type v₁} {OS : Type v₂}
variable [Behaves T OT] [Behaves S OS]

def FSim (Rin : X → Y → Prop) (R : OT → OS → Prop) (f : X → T) (g : Y → S) : Prop :=
  ∀ x y, Rin x y → Sim R (f x) (g y)

def FEquiv (Rin : X → Y → Prop) (R : OT → OS → Prop) (f : X → T) (g : Y → S) : Prop :=
  ∀ x y, Rin x y → Equiv R (f x) (g y)

/-- Conditional equivalence on one input type: `f` and `g` agree except where `Bad` holds. -/
def EquivOn (Bad : X → Prop) (R : OT → OS → Prop) (f : X → T) (g : X → S) : Prop :=
  ∀ x, ¬ Bad x → Equiv R (f x) (g x)

/-- `EquivOn` bounds the set of inputs on which the two functions differ. -/
theorem EquivOn.changed_subset {Bad : X → Prop} {R : OT → OS → Prop} {f : X → T} {g : X → S}
    (h : EquivOn Bad R f g) : ∀ x, ¬ Equiv R (f x) (g x) → Bad x :=
  fun x hx => Classical.byContradiction fun hb => hx (h x hb)

end

/-! ## The `Simulates` typeclass

`Simulates T S` says how to compare a target computation of type `T` with a source of type
`S`.  The default instance uses the outcome semantics of both sides and the representation
relation `Corr` between their outcome types, so `t ⊑ s` works for any pair of encodings once
their outcome types have a `Corr` instance (`EquivLean.Repr`).  Special pairs can override
it with a more specific instance. -/

/-- Representation correspondence: `corr a b` says that `a` (target side) represents the same
observable value as `b` (source side). -/
class Corr (A : Type u₁) (B : Type u₂) where
  corr : A → B → Prop

class Simulates (T : Type u₁) (S : Type u₂) where
  /-- `sim t s`: `t` simulates `s`. -/
  sim : T → S → Prop

instance (priority := low) instSimulatesOfBehaves {T : Type u₁} {S : Type u₂}
    {OT : Type v₁} {OS : Type v₂} [Behaves T OT] [Behaves S OS] [Corr OT OS] :
    Simulates T S where
  sim t s := Sim Corr.corr t s

@[inherit_doc] scoped infix:50 " ⊑ " => Simulates.sim

/-- `t ≈ s`: simulation both ways, with the outcome relation from `Corr`. -/
def Equivalent {T : Type u₁} {S : Type u₂} {OT : Type v₁} {OS : Type v₂}
    [Behaves T OT] [Behaves S OS] [Corr OT OS] (t : T) (s : S) : Prop :=
  Equiv Corr.corr t s

@[inherit_doc] scoped infix:50 " ≈ " => Equivalent

end EquivLean
