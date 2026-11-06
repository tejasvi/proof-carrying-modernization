/-
# Control-flow equations with proofs

`execSentences_nil/cons` and `runFrom_zero/succ` in `cobol_eval` are `rfl` lemmas, so `simp` uses
them without recording a proof, and the kernel re-derives each unfolding of the structural
recursion when it checks the composed proof.  On a concrete statement it then evaluates the
statement on the symbolic state; for a `COMP-5` receiver that evaluation reaches `fitBin`'s
range test `v < 2 ^ 32`, which the kernel reduces through `Nat.sub` in unary ("deep recursion").
The primed copies below have the same statements but proofs that are not `rfl`, so `simp`
records them as rewrites: `cobol_sym [-execSentences_cons, execSentences_cons', …]`
(`cobolEvalP` below lists all four swaps).
-/
import Cobol

namespace Cobol.Stm

section
variable (P : Program) (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (st : State)

theorem execSentences_nil' : Sem.execSentences P env rec fuel [] st = (.normal, st) :=
  Eq.trans (execSentences_nil P env rec fuel st) (Eq.refl _)

theorem execSentences_cons' (s : List Stmt) (ss : List (List Stmt)) :
    Sem.execSentences P env rec fuel (s :: ss) st =
      match Sem.execStmts P env rec fuel s st with
      | (.normal, st1) | (.nextSentence, st1) => Sem.execSentences P env rec fuel ss st1
      | r => r :=
  Eq.trans (execSentences_cons P env rec fuel st s ss) (Eq.refl _)

theorem runFrom_zero' (k : Nat) : Sem.runFrom P env 0 k st = (.outOfFuel, st) :=
  Eq.trans (runFrom_zero P env st k) (Eq.refl _)

theorem runFrom_succ' (n k : Nat) :
    Sem.runFrom P env (n + 1) k st =
      match P.paras[k]? with
      | none => (.stop .endOfProgram, st)
      | some para =>
        match Sem.execSentences P env (Sem.runFrom P env n) n para.body st with
        | (.normal, st1) | (.exitPara, st1) => Sem.endOfPara (Sem.runFrom P env n) st1.slots k st1
        | (.exitSection, st1) =>
          Sem.endOfPara (Sem.runFrom P env n) st1.slots (P.sectionEnd k) st1
        | (.goto l, st1) => Sem.runFrom P env n l st1
        | (.exitPerform, st1) | (.exitCycle, st1) | (.nextSentence, st1) =>
          (.fault (.unsupported "EXIT PERFORM outside an inline PERFORM"), st1)
        | r => r :=
  Eq.trans (runFrom_succ P env st n k) (Eq.refl _)

end

/-- `runFrom_succ` with the paragraph lookup as `Option.elim`, whose reduction on `some` is the
recorded rewrite `Option.elim_some'` (the `match` on `some para` would be a definitional step
between two `match`es, which the kernel checks by unfolding both). -/
theorem runFrom_succ_elim (P : Program) (env : Env) (st : State) (n k : Nat) :
    Sem.runFrom P env (n + 1) k st =
      (P.paras[k]?).elim (.stop .endOfProgram, st) fun para =>
        match Sem.execSentences P env (Sem.runFrom P env n) n para.body st with
        | (.normal, st1) | (.exitPara, st1) => Sem.endOfPara (Sem.runFrom P env n) st1.slots k st1
        | (.exitSection, st1) =>
          Sem.endOfPara (Sem.runFrom P env n) st1.slots (P.sectionEnd k) st1
        | (.goto l, st1) => Sem.runFrom P env n l st1
        | (.exitPerform, st1) | (.exitCycle, st1) | (.nextSentence, st1) =>
          (.fault (.unsupported "EXIT PERFORM outside an inline PERFORM"), st1)
        | r => r := by
  rw [runFrom_succ]
  cases P.paras[k]? <;> rfl

theorem Option.elim_some' {α β : Type} (a : α) (b : β) (f : α → β) :
    (some a).elim b f = f a :=
  Eq.trans (Eq.refl (f a)) (Eq.refl _)

theorem Option.elim_none' {α β : Type} (b : β) (f : α → β) :
    (none : Option α).elim b f = b :=
  Eq.trans (Eq.refl b) (Eq.refl _)

open Lean Meta in
/-- Whether simp treats each lemma as a definitional (`dsimp`) lemma. -/
elab "#stm_rfl_check" : command => Elab.Command.liftTermElabM do
  for n in [``execSentences_cons, ``execSentences_cons', ``runFrom_succ, ``runFrom_succ',
      ``runFrom_succ_elim, ``Option.elim_some'] do
    logInfo m!"{n}: rfl = {← isRflTheorem n}"

#stm_rfl_check

end Cobol.Stm
