/-
# Paragraph loops by `GO TO`: induction instead of unrolling

A paragraph `k` that processes one input item and then goes back to itself with `GO TO k`, and
leaves with `GO TO e` once the items are used up (CBSTM03A's `8500-READTRNX-READ`), is a loop of
`Sem.runFrom`: each pass consumes one unit of paragraph fuel.  `runFrom_goto_loop` replaces the
whole loop by its result, given an invariant `Inv` indexed by the items still to process: one
pass from `Inv (x :: xs)` ends with `GO TO k` in a state satisfying `Inv xs`, and the pass from
`Inv []` ends with `GO TO e` in a state satisfying `Done`.  The passes may use up to `c` units of
fuel themselves (a linked `CALL` runs the called program's paragraphs).

Used by symbolic execution as follows: the run's fuel is an opaque `F + d`, where `d` is the
number of paragraph transitions before the loop, so that symbolic execution stops at
`runFrom P env F k st`; then `F = m + xs.length + 1` is substituted and the lemma rewrites the
loop to `runFrom P env m e st'`, where symbolic execution continues.
-/
import Cobol

namespace Cobol

theorem runFrom_goto_loop {β : Type} {P : Program} {env : Env} {k e : Nat} {para : Paragraph}
    (hk : P.paras[k]? = some para) (c : Nat)
    (Inv : List β → State → Prop) (Done : State → Prop)
    (hstep : ∀ x xs st m, c ≤ m → Inv (x :: xs) st →
      (Sem.execSentences P env (Sem.runFrom P env m) m para.body st).1 = .goto k ∧
        Inv xs (Sem.execSentences P env (Sem.runFrom P env m) m para.body st).2)
    (hlast : ∀ st m, c ≤ m → Inv [] st →
      (Sem.execSentences P env (Sem.runFrom P env m) m para.body st).1 = .goto e ∧
        Done (Sem.execSentences P env (Sem.runFrom P env m) m para.body st).2) :
    ∀ (xs : List β) (st : State) (m : Nat), c ≤ m → Inv xs st →
      ∃ st', Sem.runFrom P env (m + xs.length + 1) k st = Sem.runFrom P env m e st' ∧ Done st' := by
  intro xs
  induction xs with
  | nil =>
    intro st m hm hinv
    obtain ⟨h1, h2⟩ := hlast st m hm hinv
    refine ⟨_, ?_, h2⟩
    have hX : Sem.execSentences P env (Sem.runFrom P env m) m para.body st =
        (.goto e, (Sem.execSentences P env (Sem.runFrom P env m) m para.body st).2) :=
      Prod.ext h1 rfl
    simp only [List.length_nil, Nat.add_zero]
    rw [Sem.runFrom]
    simp only [hk]
    rw [hX]
  | cons x xs ih =>
    intro st m hm hinv
    obtain ⟨h1, h2⟩ := hstep x xs st (m + xs.length + 1) (by omega) hinv
    obtain ⟨st', h3, h4⟩ := ih _ m hm h2
    refine ⟨st', ?_, h4⟩
    have hX : Sem.execSentences P env (Sem.runFrom P env (m + xs.length + 1)) (m + xs.length + 1)
          para.body st =
        (.goto k, (Sem.execSentences P env (Sem.runFrom P env (m + xs.length + 1))
          (m + xs.length + 1) para.body st).2) :=
      Prod.ext h1 rfl
    have hf : m + (x :: xs).length + 1 = (m + xs.length + 1) + 1 := by
      simp only [List.length_cons]; omega
    rw [hf, Sem.runFrom]
    simp only [hk]
    rw [hX]
    exact h3

open Lean Meta Elab Tactic

/-- `cobol_goto_loop hk e Inv Done xs c`: replace the (first) stuck `Sem.runFrom P env F k st` of
the goal, where `F` unifies with `m + xs.length + 1` and `hk : P.paras[k]? = some para`, by
`Sem.runFrom P env m e gotoState`, with `hgotoDone : Done gotoState`.  The obligations follow the
main goal: `Inv xs st`, `c ≤ m`, one pass from `Inv (x :: xs)` (ends with `GO TO k`), the pass
from `Inv []` (ends with `GO TO e`). -/
syntax "cobol_goto_loop " term:max term:max term:max term:max term:max term:max : tactic

elab_rules : tactic
  | `(tactic| cobol_goto_loop $hk $e $inv $done $xs $c) => withMainContext do
    let g ← getMainGoal
    let goal ← instantiateMVars (← g.getType)
    let some t := goal.find? (fun t => t.isAppOfArity ``Sem.runFrom 5)
      | throwError "cobol_goto_loop: no `Sem.runFrom P env F k st` in the goal"
    let targs := t.getAppArgs
    let hkE ← Term.elabTerm hk none
    let eE ← Term.elabTerm e (some (mkConst ``Nat))
    let invE ← Term.elabTerm inv none
    let doneE ← Term.elabTerm done none
    let xsE ← Term.elabTerm xs none
    let cE ← Term.elabTerm c (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let thm ← mkAppOptM ``runFrom_goto_loop
      #[none, some targs[0]!, some targs[1]!, some targs[3]!, some eE, none, some hkE, some cE,
        some invE, some doneE]
    let (mvs, _, body) ← forallMetaTelescopeReducing (← inferType thm)
    -- mvs: hstep hlast xs st m hm hinv
    unless ← isDefEq mvs[2]! xsE do throwError "cobol_goto_loop: input list has the wrong type"
    let some lhs := (← instantiateMVars body).find? (fun u => u.isAppOfArity ``Sem.runFrom 5)
      | throwError "cobol_goto_loop: internal error"
    unless ← isDefEq lhs t do
      throwError "cobol_goto_loop: the loop's fuel must be `m + xs.length + 1`, found {targs[2]!}"
    let pf ← instantiateMVars (mkAppN thm mvs)
    let g' ← g.assert `hgl (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hl := mkIdent `hgl
    let gs := mkIdent `gotoState
    let he := mkIdent `hgotoEq
    let hd := mkIdent `hgotoDone
    evalTactic (← `(tactic| obtain ⟨$gs, $he, $hd⟩ := $hl:ident))
    evalTactic (← `(tactic| rw [$he:ident]))
    let main ← getGoals
    setGoals (main ++ [mvs[6]!.mvarId!, mvs[5]!.mvarId!, mvs[0]!.mvarId!, mvs[1]!.mvarId!])

end Cobol
