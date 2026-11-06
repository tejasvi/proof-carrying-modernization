/-
# `PERFORM … VARYING` loops over data of any size

`Cobol.Logic.Loops` (`loopUntil_list`, `cobol_loop`) handles `PERFORM … UNTIL`, whose step is
`noStep`.  An inline `PERFORM VARYING … UNTIL` runs `step` (the `BY` increments) after each body
execution; `loopUntil_list_step` is the same induction with the step, and `cobol_loop_step Inv xs`
applies it to the first folded `Sem.loopUntil false …` of the goal (obligations: `Inv xs st₀`,
`xs.length < fuel`, `Inv []` ends the loop, one iteration (body, then step) preserves `Inv`).
-/
import Cobol

namespace Cobol
open Lean Meta Elab Tactic

/-- `PERFORM VARYING … UNTIL` (test before) over a list of items: induction on the list. -/
theorem loopUntil_list_step {β : Type} {cond : State → SemM Bool} {body step : State → Sem.Res}
    (Inv : List β → State → Prop)
    (hdone : ∀ st, Inv [] st → cond st = .ok true)
    (hstep : ∀ x xs st, Inv (x :: xs) st →
      cond st = .ok false ∧ (body st).1 = .normal ∧ (step (body st).2).1 = .normal ∧
        Inv xs (step (body st).2).2)
    (xs : List β) (n : Nat) (st : State) (hinv : Inv xs st) (hn : xs.length < n) :
    ∃ st', Sem.loopUntil false cond body step n st = (.normal, st') ∧ Inv [] st' := by
  induction xs generalizing n st with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    exact ⟨st, by rw [loopUntil_succ]; simp [hdone st hinv], hinv⟩
  | cons x xs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hc, hb, hs, hi⟩ := hstep x xs st hinv
    obtain ⟨st', h1, h2⟩ := ih m (step (body st).2).2 hi (by simp at hn; omega)
    refine ⟨st', ?_, h2⟩
    rw [loopUntil_succ]
    have eb : body st = (.normal, (body st).2) := Prod.ext hb rfl
    have es : step (body st).2 = (.normal, (step (body st).2).2) := Prod.ext hs rfl
    simp only [Bool.false_eq_true, ↓reduceIte, hc]
    rw [eb]
    simp only
    rw [es]
    exact h1

/-- Find the first `Sem.loopUntil false …` application in `e`. -/
private def findLoopStep? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t => t.isAppOfArity ``Sem.loopUntil 6 && (t.getArg! 0).isConstOf ``Bool.false

/-- `cobol_loop_step Inv xs`: `cobol_loop` for loops with a step (`PERFORM VARYING`). -/
syntax "cobol_loop_step " term:max term:max : tactic

elab_rules : tactic
  | `(tactic| cobol_loop_step $inv $xs) => withMainContext do
    let g ← getMainGoal
    let some loop := findLoopStep? (← instantiateMVars (← g.getType))
      | throwError "cobol_loop_step: no folded `Sem.loopUntil false …` in the goal"
    let args := loop.getAppArgs
    let invE ← Term.elabTerm inv none
    let xsE ← Term.elabTerm xs none
    Term.synthesizeSyntheticMVarsNoPostponing
    let thm ← mkAppOptM ``loopUntil_list_step #[none, args[1]!, args[2]!, args[3]!, invE]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType thm)
    -- hdone hstep xs n st hinv hn
    unless ← isDefEq mvs[2]! xsE do throwError "cobol_loop_step: input list has the wrong type"
    unless ← isDefEq mvs[3]! args[4]! do throwError "cobol_loop_step: fuel"
    unless ← isDefEq mvs[4]! args[5]! do throwError "cobol_loop_step: state"
    let pf ← instantiateMVars (mkAppN thm mvs)
    let g' ← g.assert `hloop (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hl := mkIdent `hloop
    let ls := mkIdent `loopState
    let he := mkIdent `hloopEq
    let hi := mkIdent `hloopInv
    evalTactic (← `(tactic| obtain ⟨$ls, $he, $hi⟩ := $hl:ident))
    evalTactic (← `(tactic| rw [$he:ident]))
    let main ← getGoals
    setGoals (main ++ [mvs[5]!.mvarId!, mvs[6]!.mvarId!, mvs[0]!.mvarId!, mvs[1]!.mvarId!])

end Cobol
