import EquivLean.Core.Sim
import Cobol

/-!
# COBOL (coblean) computations as `Behaves` instances

coblean gives a program `P : Cobol.Program` (from `cobol_program P from "p.ir.json"`) the
meaning `P.run env fuel st : Sem.Res = Signal × State`: a deterministic interpreter with a
fuel bound.  A closed COBOL computation is therefore just its result: `Exec` wraps a
`Sem.Res`, and `Cobol.run P env fuel st` is the run of a whole program.  The same type also
describes the pieces the bridge needs (one `PERFORM … UNTIL` loop, see `Loops.lean`).

## Outcomes and going wrong

The outcome of a run is the final signal and state (`Signal × State`).  Its signal decides
whether the run is *safe*:

* **unsafe** (no obligation on the other side of a simulation, never an outcome):
  - `outOfFuel`: fuel is a proof device, not behaviour (`Cobol/Sem/Exec.lean`: theorems are
    stated for a sufficient fuel);
  - `fault (unsupported _)`: the program left the modelled fragment (recursive `PERFORM`,
    return into an abandoned `PERFORM`, an unmodelled `CALL`, …);
  - `fault sizeUndefined`, `fault overlap`, `fault range`: the result is undefined in
    COBOL (unpredictable size-error results, overlapping `MOVE`, subscript out of range
    without `SSRANGE`);
* **observable**:
  - every `stop k` (`STOP RUN`, `GOBACK`, `EXIT PROGRAM`, end of the procedure division),
    and every other control signal a partial computation can end with;
  - the abends `fault invalidData` (S0C7, a numeric item without a valid encoding),
    `fault divByZero` (S0CB/S0C9), `fault (io status)` (an unsuccessful I/O statement with no
    `AT END`/`INVALID KEY`/`FILE STATUS` handling) and `fault (abend code)` (`CALL 'CEE3ABD'`):
    they are what IBM Enterprise COBOL does, so a rewrite has to reproduce them (as an
    exception or a panic).  Statements outside the IR fault with `unsupported` (unsafe).

The instance is `Total` and `Det`.  `wp (Cobol.run P env fuel st) Q` unfolds to
`Ok (P.run env fuel st) ∧ Q (P.run env fuel st)` (`wp_run`), where coblean's symbolic
executor `cobol_sym` evaluates the run; `cobol_wp [h…] (at h)` does both steps.
-/

open Cobol

namespace EquivLean.Cobol

/-- Faults that are observable abends of the program: invalid numeric data (IBM S0C7), division
by zero (S0CB/S0C9), an unsuccessful I/O statement the program does not handle (IBM abends with
the file status), and an explicit `CALL 'CEE3ABD'`. -/
def abend : Fault → Bool
  | .invalidData => true
  | .divByZero => true
  | .io _ => true
  | .abend _ => true
  | _ => false

/-- A completion signal that is an observable outcome: neither out of fuel nor a fault outside
the model or with an undefined result. -/
def obsSig : Signal → Bool
  | .outOfFuel => false
  | .fault f => abend f
  | _ => true

/-- A result is a safe, observable outcome. -/
def Ok (r : Sem.Res) : Prop := obsSig r.1 = true

instance (r : Sem.Res) : Decidable (Ok r) := inferInstanceAs (Decidable (obsSig r.1 = true))

/-- A closed COBOL computation, described by its (deterministic) result. -/
structure Exec where
  res : Sem.Res

/-- The run of program `P` with call environment `env` and fuel `fuel` from state `st`. -/
def run (P : Program) (env : Env) (fuel : Nat) (st : State) : Exec := ⟨P.run env fuel st⟩

instance instBehavesExec : Behaves Exec (Signal × State) where
  Runs c o := o = c.res ∧ Ok c.res
  Safe c := Ok c.res

instance : Behaves.Total Exec := ⟨fun c h => ⟨c.res, rfl, h⟩⟩
instance : Behaves.Det Exec := ⟨fun _ _ _ h₁ h₂ => h₁.1.trans h₂.1.symm⟩

/-! ## Evaluation lemmas -/

@[simp] theorem runs_exec_iff (r : Sem.Res) (o : Signal × State) :
    Runs (Exec.mk r) o ↔ o = r ∧ Ok r := Iff.rfl

@[simp] theorem safe_exec_iff (r : Sem.Res) : Safe (Exec.mk r) ↔ Ok r := Iff.rfl

@[simp] theorem wp_exec (r : Sem.Res) (Q : Signal × State → Prop) :
    wp (Exec.mk r) Q ↔ Ok r ∧ Q r :=
  ⟨fun h => ⟨h.1, h.2 r ⟨rfl, h.1⟩⟩, fun ⟨h, hq⟩ => ⟨h, fun _ ⟨ho, _⟩ => ho ▸ hq⟩⟩

theorem wp_run (P : Program) (env : Env) (fuel : Nat) (st : State) (Q : Signal × State → Prop) :
    wp (run P env fuel st) Q ↔ Ok (P.run env fuel st) ∧ Q (P.run env fuel st) :=
  wp_exec _ Q

@[simp, cobol_eval] theorem abend_invalidData : abend .invalidData = true := rfl
@[simp, cobol_eval] theorem abend_divByZero : abend .divByZero = true := rfl
@[simp, cobol_eval] theorem abend_range : abend .range = false := rfl
@[simp, cobol_eval] theorem abend_overlap : abend .overlap = false := rfl
@[simp, cobol_eval] theorem abend_sizeUndefined : abend .sizeUndefined = false := rfl
@[simp, cobol_eval] theorem abend_unsupported (w : String) : abend (.unsupported w) = false := rfl

@[simp, cobol_eval] theorem obsSig_outOfFuel : obsSig .outOfFuel = false := rfl
@[simp, cobol_eval] theorem obsSig_fault (f : Fault) : obsSig (.fault f) = abend f := rfl
@[simp, cobol_eval] theorem obsSig_stop (k : StopKind) : obsSig (.stop k) = true := rfl
@[simp, cobol_eval] theorem obsSig_normal : obsSig .normal = true := rfl
@[simp, cobol_eval] theorem obsSig_goto (p : Nat) : obsSig (.goto p) = true := rfl
@[simp, cobol_eval] theorem obsSig_ret (s : Nat) : obsSig (.ret s) = true := rfl
@[simp, cobol_eval] theorem obsSig_exitPerform : obsSig .exitPerform = true := rfl
@[simp, cobol_eval] theorem obsSig_exitCycle : obsSig .exitCycle = true := rfl
@[simp, cobol_eval] theorem obsSig_exitPara : obsSig .exitPara = true := rfl
@[simp, cobol_eval] theorem obsSig_exitSection : obsSig .exitSection = true := rfl
@[simp, cobol_eval] theorem obsSig_nextSentence : obsSig .nextSentence = true := rfl

@[simp, cobol_eval] theorem ok_mk (s : Signal) (st : State) : Ok (s, st) ↔ obsSig s = true :=
  Iff.rfl

/-- Merged results (an `if` over results, left by symbolic execution when the branches end with
different signals): the observability test goes into the `if`. -/
@[cobol_eval] theorem ok_ite (c : Prop) [Decidable c] (a b : Sem.Res) :
    Ok (if c then a else b) ↔ if c then Ok a else Ok b := by
  split <;> rfl

@[cobol_eval] theorem obsSig_ite (c : Prop) [Decidable c] (a b : Signal) :
    obsSig (if c then a else b) = if c then obsSig a else obsSig b := by
  split <;> rfl

/-! ## Simulation against a COBOL source

A COBOL run is deterministic: a simulation with a COBOL source is a weakest precondition of
the target, for the source's one outcome. -/

/-- `t ⊑ s` for a COBOL source `s = Exec.mk r`: if `r` is a safe outcome, the target is safe
and all its outcomes are related to `r`. -/
theorem sim_exec_iff {T : Type _} {OT : Type _} [Behaves T OT] {R : OT → Signal × State → Prop}
    {t : T} (r : Sem.Res) : Sim R t (Exec.mk r) ↔ (Ok r → wp t (fun ot => R ot r)) := by
  constructor
  · intro h hr
    exact (sim_iff_of_runs (s := Exec.mk r) hr ⟨rfl, hr⟩).1 h
  · intro h hr
    exact (sim_iff_of_runs (s := Exec.mk r) hr ⟨rfl, hr⟩).2 (h hr) hr

/-- COBOL as the target: every outcome of the source must match the COBOL run. -/
theorem sim_exec_target_iff {S : Type _} {OS : Type _} [Behaves S OS]
    {R : Signal × State → OS → Prop} {s : S} (r : Sem.Res) :
    Sim R (Exec.mk r) s ↔ (Safe s → Ok r ∧ ∃ os, Runs s os ∧ R r os) := by
  constructor
  · intro h hs
    obtain ⟨hok, hrun⟩ := h hs
    exact ⟨hok, hrun r ⟨rfl, hok⟩⟩
  · intro h hs
    obtain ⟨hok, os, hos, hr⟩ := h hs
    exact ⟨hok, fun o ⟨ho, _⟩ => ho ▸ ⟨os, hos, hr⟩⟩

/-! ## Tactic: symbolic execution inside `wp`

`cobol_wp [h…]` turns `wp (Cobol.run P env fuel st) Q` (in the goal, or with `at h` in a
hypothesis) into `Ok r ∧ Q r` and runs coblean's symbolic executor on it, so the result `r`
is evaluated once and the observability test is decided on its signal. -/

syntax "cobol_wp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| cobol_wp $[$loc]?) => `(tactic| cobol_wp [] $[$loc]?)
  | `(tactic| cobol_wp [$xs,*] $[$loc]?) =>
    `(tactic| (simp only [run, wp_exec, ok_mk] $[$loc]?; cobol_sym [$xs,*] $[$loc]?))

end EquivLean.Cobol
