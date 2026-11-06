/-
# Loops over data of any size: induction instead of unrolling

A `PERFORM … UNTIL` whose number of iterations depends on the input (read a file until its
end) cannot be unrolled.  Symbolic execution leaves it folded when its fuel is symbolic
(`unrollLoopUntil` only unrolls numeral fuel) and stops in front of it (`stopAtLoop`: the
`match` on its result is not explored).  `cobol_loop Inv xs` then replaces the loop by its
result, using `loopUntil_list`: if a loop invariant `Inv`, indexed by the list of input items
still to process, is established before the loop, makes the loop condition true exactly when
the list is empty, and is preserved by one iteration (the body consumes one item), then the
loop ends normally in a state satisfying `Inv []`.

The obligations are about one iteration on a symbolic state, so they are proved by symbolic
execution again; the theorem holds for input lists of every length (given enough fuel).
-/
import Cobol.Logic.Eval

namespace Cobol
open Lean Meta Elab Tactic

/-- `PERFORM body UNTIL cond` (test before) over a list of items: induction on the list. -/
theorem loopUntil_list {β : Type} {cond : State → SemM Bool} {body : State → Sem.Res}
    (Inv : List β → State → Prop)
    (hdone : ∀ st, Inv [] st → cond st = .ok true)
    (hstep : ∀ x xs st, Inv (x :: xs) st →
      cond st = .ok false ∧ (body st).1 = .normal ∧ Inv xs (body st).2)
    (xs : List β) (n : Nat) (st : State) (hinv : Inv xs st) (hn : xs.length < n) :
    ∃ st', Sem.loopUntil false cond body Sem.noStep n st = (.normal, st') ∧ Inv [] st' := by
  induction xs generalizing n st with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    exact ⟨st, by rw [loopUntil_succ]; simp [hdone st hinv], hinv⟩
  | cons x xs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hc, hb, hi⟩ := hstep x xs st hinv
    obtain ⟨st', h1, h2⟩ := ih m (body st).2 hi (by simp at hn; omega)
    refine ⟨st', ?_, h2⟩
    rw [loopUntil_succ]
    have : body st = (.normal, (body st).2) := by
      cases h : body st; simp_all
    simp only [Bool.false_eq_true, ↓reduceIte, hc]
    rw [this]
    simpa [noStep_eq] using h1

/-- Find the first `Sem.loopUntil false …` application in `e`. -/
private def findLoop? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t => t.isAppOfArity ``Sem.loopUntil 6 && (t.getArg! 0).isConstOf ``Bool.false

/-- `cobol_loop Inv xs`: replace the (first) folded `PERFORM … UNTIL` loop of the goal by its
result `loopState`, with `hloopInv : Inv [] loopState`, given a loop invariant
`Inv : List β → State → Prop` and the input items `xs`.  The obligations of `loopUntil_list`
follow the main goal: `Inv xs st₀` (before the loop), `xs.length < fuel`, `Inv []` makes the
loop condition true, one iteration preserves `Inv`. -/
syntax "cobol_loop " term:max term:max : tactic

elab_rules : tactic
  | `(tactic| cobol_loop $inv $xs) => withMainContext do
    let g ← getMainGoal
    let some loop := findLoop? (← instantiateMVars (← g.getType))
      | throwError "cobol_loop: no folded `Sem.loopUntil false …` in the goal"
    let args := loop.getAppArgs
    let invE ← Term.elabTerm inv none
    let xsE ← Term.elabTerm xs none
    Term.synthesizeSyntheticMVarsNoPostponing
    let thm ← mkAppOptM ``loopUntil_list #[none, args[1]!, args[2]!, invE]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType thm)
    -- hdone hstep xs n st hinv hn
    unless ← isDefEq mvs[2]! xsE do throwError "cobol_loop: input list has the wrong type"
    unless ← isDefEq mvs[3]! args[4]! do throwError "cobol_loop: fuel"
    unless ← isDefEq mvs[4]! args[5]! do throwError "cobol_loop: state"
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
