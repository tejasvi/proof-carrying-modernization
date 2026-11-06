/-
# Loops that may stop early

`loopUntil_list` (`Cobol/Logic/Loops.lean`) needs every iteration to consume its item and go
on. Real programs also leave a loop from inside: an abend on a failed lookup or a duplicate key,
or `NEXT SENTENCE`, which passes control to the statement after the sentence's period, out of
an inline `PERFORM`. `loopUntil_list_exit` allows that: an iteration either consumes its item
(the invariant `Inv` holds for the rest) or ends the loop with a result satisfying `Exit` whose
signal neither continues the loop (`normal`, `exitCycle`) nor ends it normally (`exitPerform`).
The loop then ends normally with `Inv []`, or with a result satisfying `Exit`.

`cobol_loop_exit Inv xs Exit` replaces the first folded `PERFORM … UNTIL` of the goal by these
two outcomes: the normal one first (`loopState`, `hloopInv : Inv [] loopState`), then the exit
(`exitSig`, `exitState`, `hexitInv : Exit (exitSig, exitState)`), followed by the obligations.
For an exit with one known signal, take `Exit r := r.1 = sig ∧ P r.2` and start the exit goal
with `obtain ⟨rfl, h⟩ := hexitInv`.
-/
import Cobol.Logic.Loops

namespace Cobol
open Lean Meta Elab Tactic

/-- `PERFORM body UNTIL cond` (test before) over a list of items, where an iteration may stop
the loop with a result satisfying `Exit`. -/
theorem loopUntil_list_exit {β : Type} {cond : State → SemM Bool} {body : State → Sem.Res}
    (Inv : List β → State → Prop) (Exit : Sem.Res → Prop)
    (hdone : ∀ st, Inv [] st → cond st = .ok true)
    (hstep : ∀ x xs st, Inv (x :: xs) st → cond st = .ok false ∧
      (((body st).1 = .normal ∧ Inv xs (body st).2) ∨
        (Exit (body st) ∧ (body st).1 ≠ .normal ∧ (body st).1 ≠ .exitCycle ∧
          (body st).1 ≠ .exitPerform)))
    (xs : List β) (n : Nat) (st : State) (hinv : Inv xs st) (hn : xs.length < n) :
    (∃ st', Sem.loopUntil false cond body Sem.noStep n st = (.normal, st') ∧ Inv [] st') ∨
    (∃ r, Sem.loopUntil false cond body Sem.noStep n st = r ∧ Exit r) := by
  induction xs generalizing n st with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    exact Or.inl ⟨st, by rw [loopUntil_succ]; simp [hdone st hinv], hinv⟩
  | cons x xs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hc, ⟨hb, hi⟩ | ⟨he, h1, h2, h3⟩⟩ := hstep x xs st hinv
    · have hbody : body st = (.normal, (body st).2) := by
        cases h : body st; simp_all
      rcases ih m (body st).2 hi (by simp at hn; omega) with ⟨st', e1, e2⟩ | ⟨r, e1, e2⟩
      · refine Or.inl ⟨st', ?_, e2⟩
        rw [loopUntil_succ]
        simp only [Bool.false_eq_true, ↓reduceIte, hc]
        rw [hbody]
        simpa [noStep_eq] using e1
      · refine Or.inr ⟨r, ?_, e2⟩
        rw [loopUntil_succ]
        simp only [Bool.false_eq_true, ↓reduceIte, hc]
        rw [hbody]
        simpa [noStep_eq] using e1
    · refine Or.inr ⟨body st, ?_, he⟩
      rw [loopUntil_succ]
      simp only [Bool.false_eq_true, ↓reduceIte, hc]
      generalize body st = r at h1 h2 h3 ⊢
      obtain ⟨sg, st1⟩ := r
      simp only at h1 h2 h3
      cases sg <;> simp_all

/-- Find the first `Sem.loopUntil false …` application in `e`. -/
private def findLoopE? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t => t.isAppOfArity ``Sem.loopUntil 6 && (t.getArg! 0).isConstOf ``Bool.false

/-- `cobol_loop_exit Inv xs Exit`: replace the (first) folded `PERFORM … UNTIL` loop of the goal
by its two outcomes. First goal: the loop ended normally in `loopState`, with
`hloopInv : Inv [] loopState`. Second goal: it stopped with `(exitSig, exitState)`, with
`hexitInv : Exit (exitSig, exitState)`. Then the obligations of `loopUntil_list_exit`:
`Inv xs st₀`, `xs.length < fuel`, `Inv []` makes the loop condition true, and one iteration
either preserves `Inv` or stops with a result satisfying `Exit` (a signal other than `normal`,
`exitCycle`, `exitPerform`). -/
syntax "cobol_loop_exit " term:max term:max term:max : tactic

elab_rules : tactic
  | `(tactic| cobol_loop_exit $inv $xs $exit) => withMainContext do
    let g ← getMainGoal
    let some loop := findLoopE? (← instantiateMVars (← g.getType))
      | throwError "cobol_loop_exit: no folded `Sem.loopUntil false …` in the goal"
    let args := loop.getAppArgs
    let invE ← Term.elabTerm inv none
    let exitE ← Term.elabTerm exit none
    let xsE ← Term.elabTerm xs none
    Term.synthesizeSyntheticMVarsNoPostponing
    let thm ← mkAppOptM ``loopUntil_list_exit #[none, args[1]!, args[2]!, invE, exitE]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType thm)
    -- hdone hstep xs n st hinv hn
    unless ← isDefEq mvs[2]! xsE do throwError "cobol_loop_exit: input list has the wrong type"
    unless ← isDefEq mvs[3]! args[4]! do throwError "cobol_loop_exit: fuel"
    unless ← isDefEq mvs[4]! args[5]! do throwError "cobol_loop_exit: state"
    let pf ← instantiateMVars (mkAppN thm mvs)
    let g' ← g.assert `hloop (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    -- the names are built with `mkIdent` (not written in the quotation) so that the proof can
    -- refer to them: identifiers inside a quotation are hygienic
    let hl := mkIdent `hloop
    let ls := mkIdent `loopState
    let le := mkIdent `hloopEq
    let li := mkIdent `hloopInv
    let es := mkIdent `exitSig
    let est := mkIdent `exitState
    let ee := mkIdent `hexitEq
    let ei := mkIdent `hexitInv
    evalTactic (← `(tactic|
      rcases $hl:ident with ⟨$ls:ident, $le:ident, $li:ident⟩ |
        ⟨⟨$es:ident, $est:ident⟩, $ee:ident, $ei:ident⟩))
    let gs ← getGoals
    let some g1 := gs[0]? | throwError "cobol_loop_exit: case split failed"
    let some g2 := gs[1]? | throwError "cobol_loop_exit: case split failed"
    setGoals [g1]
    evalTactic (← `(tactic| rw [$le:ident]))
    let g1s ← getGoals
    setGoals [g2]
    evalTactic (← `(tactic| rw [$ee:ident]))
    let g2s ← getGoals
    setGoals (g1s ++ g2s ++ [mvs[5]!.mvarId!, mvs[6]!.mvarId!, mvs[0]!.mvarId!, mvs[1]!.mvarId!])

end Cobol
