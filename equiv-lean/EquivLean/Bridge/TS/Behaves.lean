import EquivLean.Core.Loop
import StrictTS.Proof.Tactics

/-!
# StrictTS bridge: observable behaviour of TypeScript computations

A translated TypeScript function `f` means `StrictTS.callFun I P fRef vs : JS TT (Val TT ret)`,
a computation in `JS TT = ExceptT Exc (StateT (World TT) Option)`.  A *closed* computation is
such a computation together with the world it starts in; it is observed through

    JS.exec m w : Option (Except Exc α × World TT)

and the core `Behaves (Option α)` instance (`EquivLean.instBehavesOption`) applies as is:

* `none` (divergence: the least fixpoint of the interpreter is undefined) goes wrong;
* every terminating run is an observable outcome `(r, w')`: a value `.ok v`, a thrown
  JavaScript exception `.error (.thrown e)` or a panic `.error (.panic msg)`, together with the
  final world `w'` (heap, console output, job queue, timers, oracles).

`Behaves.Total` and `Behaves.Det` hold (they are the core instances for `Option`).

**Panics.**  StrictTS panics where TypeScript's own typing is unsound (an out-of-bounds
`a[i]` typed `T`, `x!` on `undefined`, reading an uninitialised field, a missing `return`):
there real JavaScript would continue with `undefined`, so a panic marks a step *outside the
modelled fragment*.  The default reading above keeps panics observable (an equivalence must
match them, which is what a refactoring of the IR has to preserve).  The *strict* reading
`Strict m w` (below) makes them unsafe instead, like undefined behaviour in C: a source that
panics carries no obligation, and a target must not panic where the source does not.  Use the
strict reading to state facts about real JavaScript programs; `wp_strict_iff` reduces it to the
default reading, so all tactics work on `JS.exec`.
-/

namespace EquivLean.TS
open StrictTS

variable {TT : TypeTable} {α β : Type}

/-- Outcomes of a closed TypeScript computation (default reading). -/
abbrev Out (TT : TypeTable) (α : Type) := Except Exc α × World TT

/-- A closed call of a translated function on the world `w` (unfolds at reducible
transparency to `JS.exec`, so every `exec_*`/`ts_sym` lemma applies). -/
abbrev call (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : FunRef args ret)
    (vs : Vals TT args.toList) (w : World TT) : Option (Out TT (Val TT ret)) :=
  JS.exec (callFun I P f vs) w

/-! ## Weakest preconditions of `JS.exec` -/

theorem wp_exec_iff (m : JS TT α) (w : World TT) (Q : Out TT α → Prop) :
    wp (JS.exec m w) Q ↔ ∃ o, JS.exec m w = some o ∧ Q o :=
  wp_option_iff _ _

/-- `wp` in the match form that symbolic execution produces. -/
theorem wp_iff_match (x : Option (Out TT α)) (Q : Out TT α → Prop) :
    wp x Q ↔ (match x with | some o => Q o | none => False) := by
  cases x <;> simp

theorem wp_of_eq {x : Option (Out TT α)} {o : Out TT α} (h : x = some o) {Q : Out TT α → Prop}
    (hq : Q o) : wp x Q := by
  subst h; simpa using hq

/-- The bind rule, in exactly the shape `JS.exec_bind` (a `ts_sym` lemma) produces: a stuck
`match exec m w with …` (a loop or a call not yet unfolded) becomes the weakest precondition
of `exec m w` with the continuation as postcondition. -/
@[simp] theorem wp_exec_match (x : Option (Out TT α)) (k : α → World TT → Option (Out TT β))
    (Q : Out TT β → Prop) :
    wp (JS.exec_bind.match_1 (fun _ => Option (Out TT β)) x k
        (fun e w' => some (.error e, w')) (fun _ => none)) Q ↔
      wp x (fun o => match o with
        | (.ok a, w') => wp (k a w') Q
        | (.error e, w') => Q (.error e, w')) := by
  rcases x with _ | ⟨_ | a, w'⟩ <;> simp

/-- The bind rule on `JS.exec` itself. -/
theorem wp_exec_bind (m : JS TT α) (f : α → JS TT β) (w : World TT) (Q : Out TT β → Prop) :
    wp (JS.exec (m >>= f) w) Q ↔
      wp (JS.exec m w) (fun o => match o with
        | (.ok a, w') => wp (JS.exec (f a) w') Q
        | (.error e, w') => Q (.error e, w')) := by
  rw [JS.exec_bind]
  exact wp_exec_match _ _ _

theorem wp_exec_pure (a : α) (w : World TT) (Q : Out TT α → Prop) :
    wp (JS.exec (pure a : JS TT α) w) Q ↔ Q (.ok a, w) := by
  simp [JS.exec_pure]

/-- Outcomes of an executed computation are determined: `exec` is a function. -/
theorem runs_exec_iff (m : JS TT α) (w : World TT) (o : Out TT α) :
    Runs (JS.exec m w) o ↔ JS.exec m w = some o := Iff.rfl

theorem safe_exec_iff (m : JS TT α) (w : World TT) :
    Safe (JS.exec m w) ↔ (JS.exec m w).isSome = true := Iff.rfl

/-- Simulation against a source whose run is known (the usual way to use a functional
specification of the source, e.g. a `StrictTS` `…_spec` lemma). -/
theorem sim_exec_of_eq {OT : Type} {T : Type} [Behaves T OT] {R : OT → Out TT α → Prop}
    {t : T} {m : JS TT α} {w : World TT} {o : Out TT α} (h : JS.exec m w = some o) :
    Sim R t (JS.exec m w) ↔ wp t (fun ot => R ot o) := by
  rw [h]
  exact sim_iff_of_runs (s := (some o : Option (Out TT α))) rfl rfl

/-- Equality of two runs (the form of `StrictTS`'s differential theorems) is equivalence with
equal outcomes. -/
theorem equiv_of_exec_eq {m₁ : JS TT α} {m₂ : JS TT α} {w₁ w₂ : World TT}
    (h : JS.exec m₁ w₁ = JS.exec m₂ w₂) : Equiv (· = ·) (JS.exec m₁ w₁) (JS.exec m₂ w₂) := by
  rw [h]; exact Equiv.refl _

/-! ## Simulation of computed runs

After symbolic execution both sides of a step are explicit (`some o` or `none`). -/

section
variable {A B : Type}

@[simp] theorem sim_some_some {R : A → B → Prop} (a : A) (b : B) :
    Sim R (some a) (some b) ↔ R a b := by
  constructor
  · intro h
    obtain ⟨os, hos, hr⟩ := (h rfl).2 a rfl
    cases Option.some.inj hos
    exact hr
  · intro hr _
    exact ⟨rfl, fun ot hot => ⟨b, rfl, (Option.some.inj hot) ▸ hr⟩⟩

@[simp] theorem sim_none_source {T : Type} [Behaves T A] {R : A → B → Prop} (t : T) :
    Sim R t (none : Option B) ↔ True :=
  ⟨fun _ => trivial, fun _ h => absurd h Bool.false_ne_true⟩

@[simp] theorem sim_none_some {R : A → B → Prop} (b : B) :
    Sim R (none : Option A) (some b) ↔ False :=
  ⟨fun h => Bool.false_ne_true (h rfl).1, False.elim⟩

/-- A computed target against any total source (e.g. an Aeneas `Result`). -/
theorem sim_some_of_wp {S : Type} [Behaves S B] [Behaves.Total S] {R : A → B → Prop} {a : A}
    {s : S} (h : wp s (fun os => R a os)) : Sim R (some a) s := fun hs =>
  let ⟨os, hos, hr⟩ := wp_exists ⟨hs, h.2⟩
  ⟨rfl, fun _ hot => ⟨os, hos, (Option.some.inj hot) ▸ hr⟩⟩

/-- Any target against a computed source. -/
theorem sim_some_iff {T : Type} [Behaves T A] {R : A → B → Prop} {t : T} (b : B) :
    Sim R t (some b) ↔ wp t (fun ot => R ot b) :=
  sim_iff_of_runs (s := (some b : Option B)) rfl rfl

end

/-! ## The strict reading: panics are unsafe -/

/-- Outcomes of the strict reading: a value or a thrown JavaScript exception, and the final
world. -/
abbrev SOut (TT : TypeTable) (α : Type) := Except ErrVal α × World TT

/-- A strict outcome as a default outcome. -/
def SOut.toOut : SOut TT α → Out TT α
  | (.ok a, w) => (.ok a, w)
  | (.error e, w) => (.error (.thrown e), w)

/-- A closed TypeScript computation observed with panics as unsafe. -/
structure Strict (TT : TypeTable) (α : Type) where
  m : JS TT α
  w : World TT

/-- Strict reading: the outcomes are the terminating runs that do not panic; a run is safe if
it terminates without panicking. -/
instance instBehavesStrict : Behaves (Strict TT α) (SOut TT α) where
  Runs c o := JS.exec c.m c.w = some o.toOut
  Safe c := ∃ o : SOut TT α, JS.exec c.m c.w = some o.toOut

theorem SOut.toOut_inj {o₁ o₂ : SOut TT α} (h : o₁.toOut = o₂.toOut) : o₁ = o₂ := by
  rcases o₁ with ⟨_ | a₁, w₁⟩ <;> rcases o₂ with ⟨_ | a₂, w₂⟩ <;>
    simp_all [SOut.toOut]

instance : Behaves.Total (Strict TT α) := ⟨fun _ h => h⟩
instance : Behaves.Det (Strict TT α) :=
  ⟨fun _ _ _ h₁ h₂ => SOut.toOut_inj (Option.some.inj (h₁.symm.trans h₂))⟩

/-- The strict reading is the default reading with panics excluded. -/
theorem wp_strict_iff (m : JS TT α) (w : World TT) (Q : SOut TT α → Prop) :
    wp (Strict.mk m w) Q ↔ wp (JS.exec m w) (fun o => match o with
      | (.ok a, w') => Q (.ok a, w')
      | (.error (.thrown e), w') => Q (.error e, w')
      | (.error (.panic _), _) => False) := by
  constructor
  · rintro ⟨⟨o, ho⟩, hq⟩
    change JS.exec m w = some o.toOut at ho
    refine ⟨by rw [ho]; rfl, fun o' ho' => ?_⟩
    change JS.exec m w = some o' at ho'
    rw [ho] at ho'
    obtain rfl := Option.some.inj ho'
    rcases o with ⟨_ | a, w'⟩ <;> exact hq _ ho
  · rintro ⟨hs, hq⟩
    rcases hx : JS.exec m w with _ | ⟨r, w'⟩
    · rw [hx] at hs; exact (Bool.false_ne_true hs).elim
    · have h1 := hq _ hx
      rcases r with (e | msg) | a
      · refine ⟨⟨(.error e, w'), hx⟩, fun o ho => ?_⟩
        change JS.exec m w = some o.toOut at ho
        rw [hx] at ho
        have := SOut.toOut_inj (o₁ := (.error e, w')) (Option.some.inj ho)
        subst this; exact h1
      · exact h1.elim
      · refine ⟨⟨(.ok a, w'), hx⟩, fun o ho => ?_⟩
        change JS.exec m w = some o.toOut at ho
        rw [hx] at ho
        have := SOut.toOut_inj (o₁ := (.ok a, w')) (Option.some.inj ho)
        subst this; exact h1

/-- A default-reading simulation whose outcome relation never relates a target panic to
anything, and relates only non-panicking source outcomes, gives a strict-reading simulation. -/
theorem Sim.strict {R : SOut TT α → SOut TT β → Prop} {m₁ : JS TT α} {m₂ : JS TT β}
    {w₁ w₂ : World TT}
    (h : ∀ Q : Out TT β → Prop, wp (JS.exec m₂ w₂) Q →
      (∀ o, Q o → ∀ msg w', o ≠ (.error (.panic msg), w')) →
      wp (JS.exec m₁ w₁) (fun o₁ => ∃ o₂ : SOut TT β, Q o₂.toOut ∧
        ∃ s₁ : SOut TT α, o₁ = s₁.toOut ∧ R s₁ o₂)) :
    Sim R (Strict.mk m₁ w₁) (Strict.mk m₂ w₂) := by
  refine sim_iff_wp.2 fun Q hs => ?_
  rw [wp_strict_iff] at hs ⊢
  let Q' : Out TT β → Prop := fun o => match o with
    | (.ok a, w') => Q (.ok a, w')
    | (.error (.thrown e), w') => Q (.error e, w')
    | (.error (.panic _), _) => False
  have hnp : ∀ o, Q' o → ∀ msg w', o ≠ (.error (.panic msg), w') := by
    rintro o ho msg w' rfl; exact ho
  refine wp_mono (h Q' hs hnp) fun o₁ ⟨o₂, hq, s₁, ho₁, hr⟩ => ?_
  subst ho₁
  rcases s₁ with ⟨_ | a₁, w₁'⟩ <;>
  · refine ⟨o₂, ?_, hr⟩
    rcases o₂ with ⟨_ | a₂, w₂'⟩ <;> exact hq

/-- Equal default outcomes give equal strict outcomes: a theorem `Equiv (· = ·)` about the IR
(panics matched) is also one about the strict reading (panics unsafe). -/
theorem Sim.strict_of_eq {m₁ m₂ : JS TT α} {w₁ w₂ : World TT}
    (h : Sim (· = ·) (JS.exec m₁ w₁) (JS.exec m₂ w₂)) :
    Sim (· = ·) (Strict.mk m₁ w₁) (Strict.mk m₂ w₂) := by
  rintro ⟨o, ho⟩
  change JS.exec m₂ w₂ = some o.toOut at ho
  have hs : Safe (JS.exec m₂ w₂) := by rw [ho]; rfl
  obtain ⟨_, hrun⟩ := h hs
  have h1 : (JS.exec m₁ w₁).isSome = true := (h hs).1
  obtain ⟨o₁, ho₁⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨os, hos, hr⟩ := hrun o₁ ho₁
  have : os = o.toOut := Option.some.inj (hos.symm.trans ho)
  subst this; subst hr
  refine ⟨⟨o, ho₁⟩, fun o' ho' => ⟨o', ?_, rfl⟩⟩
  change JS.exec m₂ w₂ = some o'.toOut
  change JS.exec m₁ w₁ = some o'.toOut at ho'
  rw [ho, ← SOut.toOut_inj (Option.some.inj (ho₁.symm.trans ho'))]

theorem Equiv.strict_of_eq {m₁ m₂ : JS TT α} {w₁ w₂ : World TT}
    (h : Equiv (· = ·) (JS.exec m₁ w₁) (JS.exec m₂ w₂)) :
    Equiv (· = ·) (Strict.mk m₁ w₁) (Strict.mk m₂ w₂) :=
  ⟨Sim.strict_of_eq h.1, (Sim.strict_of_eq (h.2.mono fun _ _ e => e.symm)).mono fun _ _ e => e.symm⟩
end EquivLean.TS
