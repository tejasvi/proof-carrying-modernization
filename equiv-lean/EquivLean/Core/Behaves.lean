/-!
# Observable behaviour of computations

Every encoding that `equiv-lean` connects (cir2lean, cobol2lean, jimple2lean, ts2lean, Aeneas)
gives programs a meaning of its own: a function into an error/divergence monad, a state
transformer with fuel, a big-step relation, an interaction tree.  `Behaves C O` is the one
interface they all share.  It describes a *closed* computation `c : C` (all inputs, including
the initial state, are already supplied) by two predicates:

* `Runs c o`: `c` can finish with the observable outcome `o`;
* `Safe c`: `c` cannot go wrong.

What "going wrong" covers is fixed by each instance and documented there: undefined
behaviour, divergence, leaving the modelled fragment, running out of fuel.  Errors that are
part of a program's observable behaviour (a thrown exception, a Rust panic, a COBOL abend)
are *outcomes*, not unsafety, so equivalence proofs must match them.

A computation whose `Safe` includes termination is `Total`; one with at most one outcome is
`Det`.  The only instance that is not total is the Jimple one (big-step semantics cannot
observe divergence), which makes every theorem with a Jimple *target* a partial-correctness
statement about that target.
-/

namespace EquivLean

universe u v w

/-- Outcome semantics of a computation type `C` with observable outcomes `O`. -/
class Behaves (C : Type u) (O : outParam (Type v)) where
  /-- `Runs c o`: running `c` can finish with outcome `o`. -/
  Runs : C → O → Prop
  /-- `Safe c`: running `c` cannot go wrong. -/
  Safe : C → Prop

export Behaves (Runs Safe)

/-- Every safe run finishes with some outcome (`Safe` includes termination). -/
class Behaves.Total (C : Type u) {O : outParam (Type v)} [Behaves C O] : Prop where
  progress : ∀ c : C, Safe c → ∃ o, Runs c o

/-- A computation has at most one outcome. -/
class Behaves.Det (C : Type u) {O : outParam (Type v)} [Behaves C O] : Prop where
  det : ∀ (c : C) o₁ o₂, Runs c o₁ → Runs c o₂ → o₁ = o₂

/-- Weakest precondition: `c` is safe and every outcome satisfies `Q`.  For a `Total`
instance this is total correctness. -/
def wp {C : Type u} {O : Type v} [Behaves C O] (c : C) (Q : O → Prop) : Prop :=
  Safe c ∧ ∀ o, Runs c o → Q o

section
variable {C : Type u} {O : Type v} [Behaves C O]

theorem wp_mono {c : C} {P Q : O → Prop} (h : wp c P) (hPQ : ∀ o, P o → Q o) : wp c Q :=
  ⟨h.1, fun o ho => hPQ o (h.2 o ho)⟩

theorem wp_safe {c : C} {Q : O → Prop} (h : wp c Q) : Safe c := h.1

theorem wp_runs {c : C} {Q : O → Prop} (h : wp c Q) {o : O} (ho : Runs c o) : Q o := h.2 o ho

theorem wp_and {c : C} {P Q : O → Prop} (hP : wp c P) (hQ : wp c Q) :
    wp c (fun o => P o ∧ Q o) :=
  ⟨hP.1, fun o ho => ⟨hP.2 o ho, hQ.2 o ho⟩⟩

/-- The strongest postcondition of a safe computation. -/
theorem wp_runs_self {c : C} (h : Safe c) : wp c (Runs c) := ⟨h, fun _ ho => ho⟩

/-- In a total instance a weakest precondition has a witness. -/
theorem wp_exists [Behaves.Total C] {c : C} {Q : O → Prop} (h : wp c Q) : ∃ o, Runs c o ∧ Q o :=
  let ⟨o, ho⟩ := Behaves.Total.progress c h.1
  ⟨o, ho, h.2 o ho⟩

theorem wp_const [Behaves.Total C] {c : C} {p : Prop} (h : wp c (fun _ => p)) : p :=
  let ⟨_, _, hp⟩ := wp_exists h
  hp

/-- A deterministic total computation that runs to `o` is described by `o` alone. -/
theorem wp_iff_of_runs [Behaves.Det C] {c : C} {o : O} (hs : Safe c) (ho : Runs c o)
    {Q : O → Prop} : wp c Q ↔ Q o :=
  ⟨fun h => h.2 o ho,
   fun h => ⟨hs, fun o' ho' => (Behaves.Det.det c o o' ho ho') ▸ h⟩⟩

end

/-! ## Behaviour of plain Lean computations

These instances are the "pure function", "error monad" and "local-state transformer" ends of
the bridge.  A state transformer `c : StateT σ m α` is observed through `c.run s₀ : m (α × σ)`;
`c : ExceptT ε m α` through `c.run : m (Except ε α)`.  No extra instance is needed for them. -/

/-- A pure value: it always finishes with itself. -/
instance instBehavesId (α : Type u) : Behaves (Id α) α where
  Runs x o := o = x
  Safe _ := True

/-- An `Except` value: both the result and the error are observable outcomes. -/
instance instBehavesExcept (ε α : Type u) : Behaves (Except ε α) (Except ε α) where
  Runs x o := o = x
  Safe _ := True

/-- An `Option` value: `none` goes wrong (divergence or failure, depending on the encoding;
`ts2lean` uses `none` for divergence). -/
instance instBehavesOption (α : Type u) : Behaves (Option α) α where
  Runs x o := x = some o
  Safe x := x.isSome

instance (α : Type u) : Behaves.Total (Id α) := ⟨fun c _ => ⟨c, rfl⟩⟩
instance (α : Type u) : Behaves.Det (Id α) := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂.symm⟩
instance (ε α : Type u) : Behaves.Total (Except ε α) := ⟨fun c _ => ⟨c, rfl⟩⟩
instance (ε α : Type u) : Behaves.Det (Except ε α) := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂.symm⟩
instance (α : Type u) : Behaves.Total (Option α) :=
  ⟨fun c h => match c, h with | some a, _ => ⟨a, rfl⟩⟩
instance (α : Type u) : Behaves.Det (Option α) :=
  ⟨fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)⟩

/-- A pure value as a computation (use it to compare a program with a Lean function). -/
abbrev pureVal {α : Type u} (a : α) : Id α := a

@[simp] theorem wp_id {α : Type u} (x : Id α) (Q : α → Prop) : wp x Q ↔ Q x :=
  ⟨fun h => h.2 x rfl, fun h => ⟨trivial, fun _ ho => ho ▸ h⟩⟩

@[simp] theorem wp_except {ε α : Type u} (x : Except ε α) (Q : Except ε α → Prop) :
    wp x Q ↔ Q x :=
  ⟨fun h => h.2 x rfl, fun h => ⟨trivial, fun _ ho => ho ▸ h⟩⟩

@[simp] theorem wp_some {α : Type u} (a : α) (Q : α → Prop) : wp (some a) Q ↔ Q a :=
  ⟨fun h => h.2 a rfl, fun h => ⟨rfl, fun _ ho => Option.some.inj ho ▸ h⟩⟩

@[simp] theorem wp_none {α : Type u} (Q : α → Prop) : wp (none : Option α) Q ↔ False :=
  ⟨fun h => Bool.false_ne_true h.1, False.elim⟩

theorem wp_option_iff {α : Type u} (x : Option α) (Q : α → Prop) :
    wp x Q ↔ ∃ a, x = some a ∧ Q a := by
  cases x <;> simp

@[simp] theorem wp_option_bind {α β : Type u} (x : Option α) (f : α → Option β) (Q : β → Prop) :
    wp (x >>= f) Q ↔ wp x (fun a => wp (f a) Q) := by
  cases x <;> simp [Option.bind]

end EquivLean
