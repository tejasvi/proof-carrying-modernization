import EquivLean.Core.Sim
import Jimple

/-!
# Java methods (JimpleLean) as `Behaves` computations

**Partial correctness.**  JimpleLean gives a method its meaning through the big-step relation
`Jimple.MExec P m args σ o`.  A diverging execution has *no* derivation, so it is invisible:
`Safe` below cannot say "terminates", and there is no `Behaves.Total` instance.  Every theorem
in which a Jimple call is the *target* of a `Sim` is therefore a partial-correctness statement
about that call: if the Java method terminates, its outcome is matched by the source.
A Jimple call can be a *source* only together with a proof that it has a terminating run
(`sim_symm_of_runs`, `runs_of_runM`) or through the relational product (`Bridge/Jimple/Rel.lean`),
which builds the source's run in lockstep with the target's.

* A closed computation is a `Call`: program, selected method, arguments (receiver first for
  instance methods) and entry state.
* An observable outcome (`Out`) is a normal return `normal v σ'` (result, final state) or an
  uncaught exception `exc e σ'` (address of the exception object in the final state; its type is
  the class of `σ'.heap e`).  Exceptions are outcomes, not unsafety.
* `Runs c o`: some execution of `c` terminates with `o`.
* `Safe c`: no execution of `c` terminates with `wrong` (ill-formed code, a library call without
  a model, behaviour the JLS leaves undefined).  Nondeterministic JDK choices (identity hash
  codes, hash iteration orders, `==` on equal value objects) are all explored.
-/

open Jimple

namespace EquivLean.Jimple

/-- A closed invocation of a selected Jimple method. -/
structure Call where
  P : Program
  m : MethodRef
  args : List Value
  σ : State

/-- Observable outcome of a Java method: normal return or uncaught exception. -/
inductive Out where
  | normal (v : Option Value) (σ : State)
  | exc (e : Addr) (σ : State)

/-- The JimpleLean outcome of an observable outcome. -/
def Out.toOutcome : Out → Outcome
  | .normal v σ => .normal v σ
  | .exc e σ => .exc e σ

/-- The final state of an outcome. -/
def Out.state : Out → State
  | .normal _ σ => σ
  | .exc _ σ => σ

/-- Partial correctness: `Runs` = a terminating, non-`wrong` execution; `Safe` = no execution ends
in `wrong`.  Divergence is neither (there is no `Total` instance). -/
instance instBehavesCall : Behaves Call Out where
  Runs c o := MExec c.P c.m c.args c.σ o.toOutcome
  Safe c := ∀ msg, ¬ MExec c.P c.m c.args c.σ (.wrong msg)

theorem runs_def (c : Call) (o : Out) : Runs c o ↔ MExec c.P c.m c.args c.σ o.toOutcome :=
  Iff.rfl

theorem safe_def (c : Call) : Safe c ↔ ∀ msg, ¬ MExec c.P c.m c.args c.σ (.wrong msg) :=
  Iff.rfl

/-- A postcondition on observable outcomes, extended to JimpleLean outcomes with `wrong`
excluded.  This is how `Spec.of` treats `wrong`. -/
def liftQ (Q : Out → Prop) : Outcome → Prop
  | .normal v σ => Q (.normal v σ)
  | .exc e σ => Q (.exc e σ)
  | .wrong _ => False

@[simp] theorem liftQ_normal (Q : Out → Prop) (v : Option Value) (σ : State) :
    liftQ Q (.normal v σ) = Q (.normal v σ) := rfl
@[simp] theorem liftQ_exc (Q : Out → Prop) (e : Addr) (σ : State) :
    liftQ Q (.exc e σ) = Q (.exc e σ) := rfl
@[simp] theorem liftQ_wrong (Q : Out → Prop) (msg : String) : liftQ Q (.wrong msg) = False := rfl
@[simp] theorem liftQ_toOutcome (Q : Out → Prop) (o : Out) : liftQ Q o.toOutcome = Q o := by
  cases o <;> rfl

/-- **`wp` of a Java call = a partial-correctness triple over `MExec`.** -/
theorem wp_iff {c : Call} {Q : Out → Prop} :
    wp c Q ↔ ∀ o, MExec c.P c.m c.args c.σ o → liftQ Q o := by
  constructor
  · intro h o ho
    cases o with
    | normal v σ' => exact h.2 (.normal v σ') ho
    | exc e σ' => exact h.2 (.exc e σ') ho
    | wrong msg => exact h.1 msg ho
  · intro h
    refine ⟨fun msg hm => h _ hm, fun o ho => ?_⟩
    have := h _ ho
    rwa [liftQ_toOutcome] at this

/-! ## Contracts -/

/-- The contract whose postcondition is a predicate on observable outcomes. -/
def specOf (pre : List Value → State → Prop) (Q : List Value → State → Out → Prop) : Spec :=
  Spec.of pre (fun args σ v σ' => Q args σ (.normal v σ')) (fun args σ e σ' => Q args σ (.exc e σ'))

theorem specOf_post (pre : List Value → State → Prop) (Q : List Value → State → Out → Prop)
    (args : List Value) (σ : State) (o : Outcome) :
    (specOf pre Q).post args σ o = liftQ (Q args σ) o := by
  cases o <;> rfl

/-- `Spec.of` postconditions are `liftQ` of their normal/exceptional parts. -/
theorem specOf_post_of (pre : List Value → State → Prop)
    (N : List Value → State → Option Value → State → Prop)
    (E : List Value → State → Addr → State → Prop) (args : List Value) (σ : State) (o : Outcome) :
    (Spec.of pre N E).post args σ o = liftQ (fun ot => match ot with
      | .normal v σ' => N args σ v σ'
      | .exc e σ' => E args σ e σ') o := by
  cases o <;> rfl

/-- A contract gives the `wp` of every call satisfying its precondition. -/
theorem wp_of_sat {P : Program} {m : MethodRef} {S : Spec} (hsat : Sat P m S)
    {args : List Value} {σ : State} (hpre : S.pre args σ) {Q : Out → Prop}
    (hpost : ∀ o, S.post args σ o → liftQ Q o) : wp (Call.mk P m args σ) Q :=
  wp_iff.2 fun o ho => hpost o (hsat args σ o hpre ho)

/-- `Sat` of a `specOf` contract is the `wp` of every call that satisfies the precondition. -/
theorem sat_specOf_iff {P : Program} {m : MethodRef} {pre : List Value → State → Prop}
    {Q : List Value → State → Out → Prop} :
    Sat P m (specOf pre Q) ↔ ∀ args σ, pre args σ → wp (Call.mk P m args σ) (Q args σ) := by
  constructor
  · intro h args σ hpre
    exact wp_of_sat h hpre fun o ho => by rwa [specOf_post] at ho
  · intro h args σ o hpre ho
    rw [specOf_post]
    exact wp_iff.1 (h args σ hpre) o ho

/-! ## From verification conditions (`jverify`) to `Sat`

`MethodVC.sat` in JimpleLean covers inlining depth `0`.  Inlining application methods
(constructors of the program's own classes, helpers) needs depth `d > 0`; without contracts the
soundness side condition `AllVC` is vacuous for every depth. -/

theorem methodVC_sat {P : Program} {d : Nat} {m : MethodRef} {S : Spec} {A : Invariants}
    {fuel : Nat} (h : MethodVC P (fun _ => none) d m S A fuel) : Sat P m S :=
  MethodVC.sat_of_allVC (Ann := { inv := fun _ => A, fuel := fun _ => fuel })
    (fun _ _ h => by cases h) h

/-! ## Sources that are deterministic and safe

A COBOL run, a Rust function on given inputs or a pure Lean value is deterministic.  Against
such a source with a known safe outcome `os`, `Sim R c s` is the partial-correctness triple
"every terminating run of `c` ends in some `ot` with `R ot os`", which is a `Sat` goal that
`jverify` proves. -/

section
universe u v
variable {Src : Type u} {OS : Type v} [Behaves Src OS]

/-- **Bridge: `Sim` from a contract.** -/
theorem sim_of_sat [Behaves.Det Src] {s : Src} {os : OS} (hs : Safe s) (hos : Runs s os)
    {R : Out → OS → Prop} {P : Program} {m : MethodRef} {args : List Value} {σ : State}
    {S : Spec} (hsat : Sat P m S) (hpre : S.pre args σ)
    (hpost : ∀ o, S.post args σ o → liftQ (fun ot => R ot os) o) :
    Sim R (Call.mk P m args σ) s :=
  (sim_iff_of_runs hs hos).2 (wp_of_sat hsat hpre hpost)

/-- **Bridge: `Sim` from verification conditions.**  The goal `MethodVC …` is what `jverify`
proves. -/
theorem sim_of_methodVC [Behaves.Det Src] {s : Src} {os : OS} (hs : Safe s) (hos : Runs s os)
    {R : Out → OS → Prop} {P : Program} {d : Nat} {m : MethodRef} {S : Spec} {A : Invariants}
    {fuel : Nat} (hvc : MethodVC P (fun _ => none) d m S A fuel) {args : List Value} {σ : State}
    (hpre : S.pre args σ) (hpost : ∀ o, S.post args σ o → liftQ (fun ot => R ot os) o) :
    Sim R (Call.mk P m args σ) s :=
  sim_of_sat hs hos (methodVC_sat hvc) hpre hpost

/-- The converse of `sim_of_sat`: `Sim` against a deterministic safe source is a triple. -/
theorem wp_of_sim [Behaves.Det Src] {s : Src} {os : OS} (hs : Safe s) (hos : Runs s os)
    {R : Out → OS → Prop} {c : Call} (h : Sim R c s) : wp c (fun ot => R ot os) :=
  (sim_iff_of_runs hs hos).1 h

/-- **The other direction.**  A Jimple call simulated by a deterministic safe source is in turn
simulated by it, provided the call has a terminating run (partial correctness cannot supply
one: take it from the interpreter with `runs_of_runM`, or from a termination argument). -/
theorem sim_symm_of_runs [Behaves.Det Src] {s : Src} {os : OS} (hs : Safe s) (hos : Runs s os)
    {R : Out → OS → Prop} {c : Call} (h : Sim R c s) (hrun : ∃ ot, Runs c ot) :
    Sim (fun os ot => R ot os) s c := by
  intro _
  refine ⟨hs, fun os' hos' => ?_⟩
  have he : os' = os := Behaves.Det.det s os' os hos' hos
  subst he
  obtain ⟨ot, hot⟩ := hrun
  exact ⟨ot, hot, (wp_of_sim hs hos h).2 ot hot⟩

/-- Equivalence with a deterministic safe source, from the contract and one terminating run. -/
theorem equiv_of_sim_of_runs [Behaves.Det Src] {s : Src} {os : OS} (hs : Safe s)
    (hos : Runs s os) {R : Out → OS → Prop} {c : Call} (h : Sim R c s)
    (hrun : ∃ ot, Runs c ot) : Equiv R c s :=
  ⟨h, sim_symm_of_runs hs hos h hrun⟩

end

/-- A terminating run found by the (sound) interpreter. -/
theorem runs_of_runM {P : Program} {fuel : Nat} {m : MethodRef} {args : List Value} {σ : State}
    {o : Out} (h : runM P fuel m args σ = some o.toOutcome) : Runs (Call.mk P m args σ) o :=
  runM_sound P fuel m args σ _ h

/-- The method of class `cls` named `name` (the first one, as in the JimpleLean examples). -/
def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

end EquivLean.Jimple
