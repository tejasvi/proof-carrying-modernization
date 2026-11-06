/-
StrictTS proof layer: `ts_eval`, concrete evaluation.

`ts_eval [lemmas]` proves statements about runs on concrete inputs (test cases, the module's
initialisation, functions applied to literals) by running the program inside the proof, with no
summary and no invariant:

* contract statements (`JS.Returns`, `JS.NoFault`, `JS.NoPanic`) are unfolded, and the world after
  module initialisation (`Testing.initWorld I program`) is computed first;
* `simp` executes the code with `ts_sym`, the call lemmas and bodies of every function of the
  program (read off its `funs` list), the closed-number evaluation of `StrictTS.Proof.F64Eval`
  and the merge sort `sortBy` on explicit lists (`sortBy_cons_cons`, `List.cons_merge_cons`);
  `Nat.add_assoc` turns the addresses of fresh cells into `w.next + k`, so that lookups past
  later allocations resolve (`w.next + 2 ≠ w.next`);
* loops are unrolled one iteration at a time (`evalLoop.eq_1`, `evalForOf.eq_1`, `evalDo.eq_1`),
  each followed by the same `simp`, as long as one is left; an array method whose callback the
  plain execution leaves stuck goes through `ts_callbacks`, and any other stuck builtin with a
  callback (`Array.from`, …) runs its definition (`evalBuiltin.eq_def`, with `List.range` of a
  literal expanded);
* a run that ends with a value closes `∃ a w', exec … = some (.ok a, w')` by `rfl`.

The implementation-approximated functions stay parameters (`I`): a run that needs `I.pow x y`
outside the cases ECMA-262 fixes, or `Math.sin`, keeps that term.
-/
import StrictTS.Proof.Auto
import StrictTS.Proof.F64Eval
import StrictTS.Testing

namespace StrictTS
open Lean Elab Tactic Meta

/-! ### `sortBy` on explicit lists -/

theorem sortBy_nil' {α : Type} (le : α → α → Bool) : sortBy le ([] : List α) = [] := by
  rw [sortBy]; simp

theorem sortBy_singleton {α : Type} (le : α → α → Bool) (a : α) : sortBy le [a] = [a] := by
  rw [sortBy]; simp

/-- One merge-sort step on a list with at least two elements (on an explicit list, `simp`
computes the split and the merge). -/
theorem sortBy_cons_cons {α : Type} (le : α → α → Bool) (a b : α) (l : List α) :
    sortBy le (a :: b :: l) =
      List.merge (sortBy le ((a :: b :: l).take ((l.length + 2) / 2)))
        (sortBy le ((a :: b :: l).drop ((l.length + 2) / 2))) le := by
  rw [sortBy, ite_eq_right_of_eq_false _ _ (by simp)]; rfl

/-- `List.range n` for a literal `n ≤ 4096` as an explicit list (the positions of `Array.from`,
`reduceRight`, … on a concrete length); used by `ts_eval`, not a `simp` lemma. -/
dsimproc reduceListRange (List.range _) := fun e => do
  let_expr List.range n := e | return .continue
  let some n ← getNatValue? n | return .continue
  unless n ≤ 4096 do return .continue
  return .done ((List.range n).foldr (fun k acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat)
    (mkNatLit k) acc) (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)))

/-! ### `ts_eval` -/

/-- The call lemmas and definitions (`X.f_call`, `X.fDef`) of the functions of the program `P`
(a constant whose value lists its functions). -/
def programCallLemmas (P : Lean.Expr) : MetaM (Array Name) := do
  let some p := P.constName? | return #[]
  let some info := (← getEnv).find? p | return #[]
  let some v := info.value? | return #[]
  let mut out := #[]
  let defs := (v.foldConsts #[] fun c acc => acc.push c).filter fun c =>
    match c with
    | .str _ s => s.endsWith "Def"
    | _ => false
  for d in defs do
    let .str pre s := d | continue
    let lem := pre.str (String.ofList (s.toList.take (s.length - 3)) ++ "_call")
    if (← getEnv).contains lem then out := out.push lem |>.push d
  return out

/-- The program of the first call `callFun I P f vs` in the goal. -/
def goalProgram (goal : Lean.Expr) : Option Lean.Expr :=
  (goal.find? fun e => e.isAppOfArity ``callFun 7).map (·.getArg! 2)

/-- Replace `Testing.initWorld I P` by the world it computes (`World.init TT` for a program
whose initialisation allocates and prints nothing). -/
def evalInitWorld : TacticM Unit := withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some iw := goal.find? fun e => e.isAppOfArity ``Testing.initWorld 3 | return
  let P := iw.getArg! 2
  let some p := P.constName? | return
  let mut unf : Array Name := #[``Testing.initWorld, p]
  let mainName := p.getPrefix.str "mainBlock"
  if (← getEnv).contains mainName then unf := unf.push mainName
  let iwS ← Term.exprToSyntax iw
  let ids ← unf.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let hw := mkIdent `hw_init
  try
    evalTactic (← `(tactic| have $hw:ident : $iwS = World.init _ := by
      (simp [ts_sym, $ids,*]) <;> rfl))
    evalTactic (← `(tactic| rw [$hw:ident]; clear $hw:ident))
  catch _ =>
    try evalTactic (← `(tactic| conv in Testing.initWorld _ _ => simp only [ts_sym, $ids,*]))
    catch _ => pure ()

/-- The simp call of `ts_eval`. -/
def evalSimp (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  evalTactic (← `(tactic| simp (config := { maxSteps := 4000000 })
    [ts_sym, JS.Returns, JS.NoFault, JS.NoPanic, sortBy_nil', sortBy_singleton, sortBy_cons_cons,
      List.cons_merge_cons, Nat.add_assoc, reduceListRange, $lemmas,*]))

/-- Run `tac`; `true` if it succeeded and changed the goals. -/
def progressed (tac : TacticM Unit) : TacticM Bool := do
  let before ← getGoals
  let beforeTys ← before.mapM fun g => do instantiateMVars (← g.getType)
  try
    tac
    let after ← getGoals
    if after.length != before.length then return true
    let afterTys ← after.mapM fun g => do instantiateMVars (← g.getType)
    return afterTys != beforeTys
  catch _ => return false

/-- `ts_eval` on the main goal. -/
def runTsEval (user : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (fuel : Nat := 400) : TacticM Unit :=
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := max ctx.maxRecDepth 20000 }) do
  try evalTactic (← `(tactic| simp only [JS.Returns, JS.NoFault, JS.NoPanic])) catch _ => pure ()
  if (← getGoals).isEmpty then return
  evalInitWorld
  let goal ← instantiateMVars (← getMainTarget)
  let calls ← match goalProgram goal with
    | some P => programCallLemmas P
    | none => pure #[]
  let mut acc := user
  for c in calls do
    acc := acc.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident))
  let lemmas := acc
  let _ ← progressed (evalSimp lemmas)
  let steps : List (TacticM Unit) := [
    do evalTactic (← `(tactic| rw [evalLoop.eq_1])); evalSimp lemmas,
    do evalTactic (← `(tactic| rw [evalForOf.eq_1])); evalSimp lemmas,
    do evalTactic (← `(tactic| rw [evalDo.eq_1])); evalSimp lemmas,
    do evalTactic (← `(tactic| ts_callbacks)); evalSimp lemmas,
    do evalTactic (← `(tactic| rw [evalBuiltin.eq_def])); evalSimp lemmas]
  for _ in [0:fuel] do
    if (← getGoals).isEmpty then return
    let mut moved := false
    for s in steps do
      if ← progressed s then moved := true; break
    unless moved do break
  if (← getGoals).isEmpty then return
  try evalTactic (← `(tactic| all_goals exact ⟨_, _, rfl⟩)) catch _ => pure ()

/-- `ts_eval [lemmas]`: prove a statement about a concrete run by executing it (see the module
comment); `lemmas` take part in every `simp` step (e.g. facts about `I`). -/
syntax (name := tsEval) "ts_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| ts_eval) => runTsEval #[]
  | `(tactic| ts_eval [$hs,*]) => runTsEval hs.getElems

end StrictTS
