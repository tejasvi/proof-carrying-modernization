/-
Regression check for a "loose bvar" PANIC (Lean core, `whnfEasyCases`) that `ts_callbacks` caused
when the goal held a call of an array method under a binder (here: inside the comparator of a
sort, bench pair 36 as difftool generates it). Not a proof: the statement ends with `sorry`; the
check is that `lean` prints no PANIC (tests/proof/check_no_panic.sh).
-/
import StrictTS
import StrictTS.Proof.Literals
set_option maxRecDepth 100000
open StrictTS StrictTS.Frontend
/- difftool: glue tactics included in every generated proof file after `import StrictTS`. The general
helpers they build on (`ts_destruct`, `ts_cell1`/`ts_cells`, the `arrayIndexNumeral` simproc) are in
StrictTS/Proof/Literals.lean; `ts_auto`, `ts_summarize` and `ts_callbacks` in StrictTS/Proof. -/
open Lean Elab Tactic Meta in
/-- Case split on the first heap lookup (closed term) in the goal, then symbolic execution with the
case hypothesis: both programs read the same cells of the same world (difftool). -/
elab "dt_heap_split" : tactic => withMainContext do
  let goal ← getMainTarget
  let some e := goal.find? (fun e => e.isAppOf ``Std.ExtDHashMap.get? && !e.hasLooseBVars)
    | throwError "dt_heap_split: no heap lookup"
  let es ← Term.exprToSyntax e
  evalTactic (← `(tactic| rcases hh : $es:term with _ | hc <;>
    simp only [ts_sym, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, and_true, true_and, hh]))

/-- Numerals of `number` as integers (bridges `OfNat` literals to the number lemmas). -/
theorem dt_lit (n : Nat) : (OfNat.ofNat n : F64) = F64.ofInt n := F64.ofNat_eq_ofInt n

/-- int32 idioms on both sides of an equation: to `BitVec 32`, then `bv_decide` (difftool). -/
macro "dt_int32" : tactic => `(tactic| (
  simp only [Val.num.injEq, F64.bxor, F64.bor, F64.band, F64.bnot, F64.shr, F64.shl, F64.sar, F64.imul,
    F64.toInt32_ofInt32, F64.toInt32_ofUint32]
  try simp only [dt_lit]
  try simp (disch := ts_safe) only [F64.toInt32_ofInt]
  first | (congr 1 <;> (try simp only [BitVec.ofInt_natCast]) <;> bv_decide) | bv_decide))

/-- Branches whose case hypotheses contradict each other (enum tags, small naturals); difftool. -/
macro "dt_contra" : tactic => `(tactic| (
  simp only [beq_iff_eq, Fin.ext_iff, Fin.val_mk, beq_self_eq_true, not_true_eq_false, eq_self_iff_true] at * <;> omega))
open Lean Elab Tactic Meta in
/-- Case split on the first `if` whose condition is a closed term, then symbolic execution with
the case hypothesis (difftool). -/
elab "dt_ite_split" : tactic => withMainContext do
  let goal ← getMainTarget
  let some e := goal.find? (fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !(e.getArg! 1).hasLooseBVars)
    | throwError "dt_ite_split: no if-then-else with a closed condition"
  let cs ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases hc : $cs <;>
    simp only [ts_sym, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, and_true, true_and, hc]))


open Lean Elab Tactic Meta in
/-- `ts_auto` without its final `simp`: unfold the calls of the functions in the goal (each once),
then summarize loops and callbacks; the remaining goals are left to the next tactics (difftool). -/
elab "dt_auto" : tactic => do
  let mut done : Array Name := #[]
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    match ← StrictTS.unfoldOneCall done with
    | some r => done := done.push r
    | none => break
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    let progress ← (do evalTactic (← `(tactic| ts_summarize)); pure true) <|>
      (do evalTactic (← `(tactic| ts_callbacks)); pure true) <|> pure false
    unless progress do break

open Lean Elab Tactic Meta in
/-- Unfold the calls of the functions in the goal, each once (the first step of `ts_auto`). -/
elab "dt_unfold" : tactic => do
  let mut done : Array Name := #[]
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    match ← StrictTS.unfoldOneCall done with
    | some r => done := done.push r
    | none => break

/-! Concrete evaluation of input-validated functions (difftool): `dt_int_cases` replaces a number
argument that the code checks with `Number.isInteger(n)`, `n < 0` and `n > m` (`m ≤ 64`) by each
of `-0, 0, …, m`; `dt_eval_calls` replaces the calls of top-level functions on closed arguments by
their values, memoized over all goals (recursion on a concrete argument unfolds each call once in
all); `dt_eval_loops` unrolls loops over closed environments one iteration at a time. -/

namespace StrictTS.DiffTool
open Lean Meta Elab Tactic

/-- Run `x` with `factor` times the current heartbeat budget (concrete evaluation of many cases). -/
def withMoreHeartbeats {α : Type} (factor : Nat) (x : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := ctx.maxHeartbeats * factor }) x

/-- `simp only [ts_sym, …]` on an expression (definitions in `unfold`, proofs in `extra`; the
default simprocs and those of `ts_sym`, `eq_self`/`iff_self` as `simp only` has them). -/
def symSimp (e : Lean.Expr) (unfold : Array Name) (extra : Array Lean.Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `ts_sym | throwError "difftool: no ts_sym simp set"
  let mut thms ← ext.getTheorems
  for n in [``eq_self, ``iff_self] do thms ← thms.addConst n
  for n in unfold do thms ← thms.addDeclToUnfold n
  for p in extra do thms ← thms.add (.other `dt_memo) #[] p
  let mut simprocs : Simp.SimprocsArray := #[← Simp.getSimprocs]
  if let some se ← Simp.getSimprocExtension? `ts_sym then simprocs := simprocs.push (← se.getSimprocs)
  let ctx ← Simp.mkContext (config := { maxSteps := 4000000 }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Simp.main e ctx (methods := Simp.mkDefaultMethodsCore simprocs)
  return r

/-- A run `JS.exec (callFun I P f args) w` of a top-level function on closed arguments. -/
def closedCall? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t => t.isAppOfArity ``JS.exec 4 && (t.getArg! 2).isAppOfArity ``callFun 7 &&
    ((t.getArg! 2).getArg! 5).isConst && !((t.getArg! 2).getArg! 6).hasFVar && !t.hasLooseBVars

/-- Memoized evaluation of a closed call: a proof of `call = value` with no call left in the value;
the inner calls of its body are evaluated first. -/
partial def evalCall (memo : IO.Ref (Array (Lean.Expr × Lean.Expr))) (call : Lean.Expr) (depth : Nat := 0) :
    MetaM (Option Lean.Expr) := do
  let lctx ← getLCtx
  -- entries made in another goal are usable when their free variables are in this context
  let usable := (← memo.get).filter fun (_, pf) => !pf.hasAnyFVar (fun fv => !lctx.contains fv)
  if let some (_, pf) := usable.find? (·.1 == call) then return some pf
  if depth > 256 then return none
  let cf := call.getArg! 2
  let some (lem, defn) ← callLemmaOf (cf.getArg! 5).constName! | return none
  let r1 ← symSimp call #[defn] (#[mkAppN (mkConst lem) #[cf.getArg! 1, cf.getArg! 6]] ++ usable.map (·.2))
  let mut pf ← r1.getProof
  let mut cur := r1.expr
  for _ in [0:64] do
    let some inner := closedCall? cur | break
    if inner == call then return none
    let some pi ← evalCall memo inner (depth + 1) | return none
    let r ← symSimp cur #[] #[pi]
    if r.expr == cur then return none
    pf ← mkEqTrans pf (← r.getProof)
    cur := r.expr
  if (cur.find? (·.isConstOf ``callFun)).isSome then return none
  memo.modify (·.push (call, pf))
  return some pf

/-- One iteration of the first loop on one side of the goal's equation, when its environment is
closed (so that its test evaluates): that side is rewritten by the loop's `evalLoop.eq_1` and
`simp only [ts_sym]`, by a proof of `side = side'` (no rewrite of the whole goal). -/
def loopStep (lhs : Bool) : TacticM Bool := withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some (ty, l, r) := goal.consumeMData.eq? | return false
  let side := if lhs then l else r
  let some loop := side.find? (·.isAppOfArity ``evalLoop 9) | return false
  if loop.getAppArgs.back!.hasFVar then return false
  let eqn := mkAppN (mkConst ``evalLoop.eq_1 loop.getAppFn.constLevels!) loop.getAppArgs
  let res ← symSimp side #[] #[eqn]
  if res.expr == side then return false
  let pf ← res.getProof
  let motive ← withLocalDeclD `x ty fun x => do
    mkLambdaFVars #[x] (← if lhs then mkEq x r else mkEq l x)
  let target' ← if lhs then mkEq res.expr r else mkEq l res.expr
  let g' ← (← getMainGoal).replaceTargetEq target' (← mkCongrArg motive pf)
  replaceMainGoal [g']
  return true

/-- The natural number of a numeral `number` literal (`OfNat.ofNat n` or `F64.ofNat n`). -/
def numeral? (c : Lean.Expr) : Option Nat :=
  if c.isAppOfArity ``OfNat.ofNat 3 then (c.getArg! 1).rawNatLit?
  else if c.isAppOfArity ``F64.ofNat 1 then (c.getArg! 0).rawNatLit? <|> (c.getArg! 0).nat?
  else none

end StrictTS.DiffTool

open Lean Elab Tactic Meta StrictTS.DiffTool in
/-- `dt_eval_calls`: in every goal, in order, replace each closed call of a top-level function by
its value (memoized across the goals), then `simp only [ts_sym]` (difftool). -/
elab "dt_eval_calls" : tactic => withMoreHeartbeats 50 do
  let memo ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let mut rest : List MVarId := []
  for g in ← getGoals do
    setGoals [g]
    for _ in [0:64] do
      if (← getGoals).isEmpty then break
      let goal ← instantiateMVars (← getMainTarget)
      let some c := closedCall? goal | break
      let some pf ← withMainContext (evalCall memo c) | throwError "dt_eval_calls: a call did not evaluate"
      let ps ← Term.exprToSyntax pf
      evalTactic (← `(tactic| simp only [ts_sym, $ps:term]))
    rest := rest ++ (← getGoals)
  setGoals rest

open Lean Elab Tactic Meta StrictTS.DiffTool in
/-- `dt_eval_loops`: unroll the loops of both sides of the goal's equation one iteration at a time
(closed environments only: each test evaluates), then `rfl` (difftool). -/
elab "dt_eval_loops" : tactic => withMoreHeartbeats 50 do
  for _ in [0:512] do
    if (← getGoals).isEmpty then return
    unless ← loopStep true do break
  for _ in [0:512] do
    if (← getGoals).isEmpty then return
    unless ← loopStep false do break
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| rfl))

open Lean Elab Tactic Meta StrictTS.DiffTool in
/-- `dt_int_guard`: succeeds when a function called in the goal tests `Number.isInteger` in its
body and compares with a numeral between 1 and 64 (a cheap check before the case split, read off
the definitions) (difftool). -/
elab "dt_int_guard" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let acc ← IO.mkRef (#[] : Array Name)
  let _ ← Core.transform goal (pre := fun t => do
    if t.isAppOfArity ``callFun 7 && (t.getArg! 5).isConst then acc.modify (·.push (t.getArg! 5).constName!)
    return .continue)
  for ref in ← acc.get do
    let some (_, defn) ← callLemmaOf ref | continue
    let some ci := (← getEnv).find? defn | continue
    let some v := ci.value? | continue
    let small := (v.find? fun t => t.isAppOfArity ``Lit.num 1 &&
      (numeral? (t.getArg! 0)).any (fun m => 0 < m && m ≤ 64)).isSome
    if (v.find? (·.isConstOf ``NumPred.isInteger)).isSome && small then return
  throwError "dt_int_guard: no Number.isInteger test with a small bound"

open Lean Elab Tactic Meta StrictTS.DiffTool in
/-- `dt_int_cases`: a number argument `n` tested by `Number.isInteger(n)`, `n < 0` and `n > m`
(`m` a numeral of at most 64) is split on these tests; the branches that fail them are closed by
`rfl` or left; in the branch that passes them, `n` is replaced by each of `-0, 0, 1, …, m`
(`F64.int_range_cases`) (difftool). -/
elab "dt_int_cases" : tactic => withMoreHeartbeats 50 do
  let goal ← instantiateMVars (← getMainTarget)
  let some ii := goal.find? (fun t => t.isAppOfArity ``F64.isInteger 1 && (t.getArg! 0).isFVar)
    | throwError "dt_int_cases: no Number.isInteger test of a variable"
  let n := ii.getArg! 0
  let isAtom (t : Lean.Expr) : Bool :=
    (t.isAppOfArity ``F64.isInteger 1 && t.getArg! 0 == n) ||
    ((t.isAppOfArity ``F64.lt 2 || t.isAppOfArity ``F64.gt 2) && t.getArg! 0 == n &&
      (numeral? (t.getArg! 1)).isSome)
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let _ ← Core.transform goal (pre := fun t => do
    if isAtom t && !(← acc.get).contains t then acc.modify (·.push t)
    return .continue)
  for a in ← acc.get do
    let name := if a.isAppOf ``F64.isInteger then `h_dt_int else if a.isAppOf ``F64.lt then `h_dt_lo else `h_dt_hi
    let aS ← Term.exprToSyntax a
    evalTactic (← `(tactic| all_goals (cases $(mkIdent name):ident : $aS:term <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Bool.or_true,
        Bool.true_or, Bool.or_false, Bool.false_or, ts_sym])))
  evalTactic (← `(tactic| all_goals try rfl))
  let mut out : List MVarId := []
  for g in ← getGoals do
    let r ← g.withContext do
      let lctx ← getLCtx
      let some dI := lctx.findFromUserName? `h_dt_int | return none
      let some dL := lctx.findFromUserName? `h_dt_lo | return none
      let some dH := lctx.findFromUserName? `h_dt_hi | return none
      let some (_, _, rI) := (← instantiateMVars dI.type).eq? | return none
      let some (_, lL, rL) := (← instantiateMVars dL.type).eq? | return none
      let some (_, lH, rH) := (← instantiateMVars dH.type).eq? | return none
      unless rI.isConstOf ``Bool.true && rL.isConstOf ``Bool.false && rH.isConstOf ``Bool.false do return none
      unless lL.isAppOfArity ``F64.lt 2 && numeral? (lL.getArg! 1) == some 0 do return none
      unless lH.isAppOfArity ``F64.gt 2 do return none
      let some m := numeral? (lH.getArg! 1) | return none
      unless m ≤ 64 do return none
      return some m
    match r with
    | none => out := out ++ [g]
    | some m =>
      -- one case per value, each a numeral (`omega` proves the disjunction from `dt_k ≤ m`)
      let disj := String.intercalate " ∨ " ((List.range (m + 1)).map fun v => s!"dt_k = {v}")
      let pats := String.intercalate " | " (List.replicate (m + 1) "rfl")
      let .ok split := Parser.runParserCategory (← getEnv) `tactic
          s!"(have h_dt_or : {disj} := by omega\n rcases h_dt_or with {pats})" | throwError "dt_int_cases: pattern"
      let sub ← Tactic.run g (do
        evalTactic (← `(tactic| rcases F64.int_range_cases (m := $(Syntax.mkNumLit (toString m))) (by decide)
          $(mkIdent `h_dt_int) $(mkIdent `h_dt_lo) $(mkIdent `h_dt_hi) with
          $(mkIdent `h_dt_z):ident | ⟨$(mkIdent `dt_k):ident, $(mkIdent `h_dt_k):ident, $(mkIdent `h_dt_e):ident⟩))
        evalTactic (← `(tactic| first | subst $(mkIdent `h_dt_z):ident | subst $(mkIdent `h_dt_e):ident))
        evalTactic (← `(tactic| all_goals (try subst $(mkIdent `h_dt_e):ident)))
        evalTactic (← `(tactic| all_goals (try ($(⟨split⟩))))))
      out := out ++ sub
  setGoals out

open Lean Meta Simp in
/-- A read of a cell through a write to another address of the heap: `(h.insert (k, a) c).get? (k', a')`
is `h.get? (k', a')` when `omega` proves `a ≠ a'` from the context, e.g. an argument array
`a' < w.next` read after an allocation at `w.next + 1` (the observational statements; difftool). -/
simproc_decl dtFreshRead (Std.ExtDHashMap.get? (Std.ExtDHashMap.insert _ _ _) _) := fun e => do
  let n := e.getAppNumArgs
  unless e.isAppOf ``Std.ExtDHashMap.get? && n ≥ 2 do return .continue
  let m := e.getArg! (n - 2)
  let key := e.getArg! (n - 1)
  let nm := m.getAppNumArgs
  unless m.isAppOf ``Std.ExtDHashMap.insert && nm ≥ 3 do return .continue
  let h := m.getArg! (nm - 3)
  let c := m.getArg! (nm - 1)
  let_expr Prod.mk _ _ k a := m.getArg! (nm - 2) | return .continue
  let_expr Prod.mk _ _ k' a' := key | return .continue
  if a == a' || a.hasLooseBVars || a'.hasLooseBVars then return .continue
  let g ← mkFreshExprMVar (← mkAppM ``Ne #[a, a'])
  let ok ← try
      let gs ← Elab.Term.TermElabM.run' (Elab.Tactic.run g.mvarId! (Elab.Tactic.evalTactic (← `(tactic| omega))))
      pure gs.isEmpty
    catch _ => pure false
  unless ok do return .continue
  let pf ← mkAppOptM ``StrictTS.JS.heap_get_insert_addr_ne #[none, h, k, k', a, a', c, ← instantiateMVars g]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

namespace Old_b35u001

/-- Named (recursive) types and classes of the program (the IR refers to the
field lists `«C».fields` below directly; `fields` is kept as documentation). -/
abbrev TT : TypeTable where
  alias := fun _ => .undef
  fields := fun _ => .nil

/-- `sortedCopy(xs: number[]): number[]` -/
def «sortedCopyRef» : FunRef tys[(.arr .num)] (.arr .num) := ⟨0, "sortedCopy"⟩

def «sortedCopyDef» : FunDef TT where
  name := "sortedCopy"
  args := tys[(.arr .num)]
  ret := (.arr .num)
  lam := .sync [⟨(.arr .num), false⟩] rfl
    (.decl ⟨(.arr .num), false⟩ (.builtin (.arrSlice .num) args[var! 0, .lit (.num 0), .none])
    (.seq (.expr (.builtin (.arrSort .num) args[var! 0, .lam [] caps[] (.sync [⟨.num, false⟩, ⟨.num, false⟩] rfl
  (.seq (.ret (.prim (.numBin .sub) args[var! 0, var! 1]))
  .nil))]))
    (.seq (.ret (var! 0))
    .nil)))

def mainBlock : Block TT [] .undef :=
  .nil

def program : Program TT where
  funs := [«sortedCopyDef»]
  globals := []
  main := mainBlock

/-! Call-unfolding lemmas: a call of a top-level function runs its body. -/

theorem «sortedCopy_call» (I : Impl) (vs : Vals TT [(.arr .num)]) :
    callFun I program «sortedCopyRef» vs = applyLam I program «sortedCopyDef».lam .nil vs := by
  rw [callFun.eq_1]; rfl

end Old_b35u001

namespace New_b35u001

/-- Named (recursive) types and classes of the program (the IR refers to the
field lists `«C».fields` below directly; `fields` is kept as documentation). -/
abbrev TT : TypeTable where
  alias := fun _ => .undef
  fields := fun _ => .nil

/-- `sortedCopy(xs: number[]): number[]` -/
def «sortedCopyRef» : FunRef tys[(.arr .num)] (.arr .num) := ⟨0, "sortedCopy"⟩

def «sortedCopyDef» : FunDef TT where
  name := "sortedCopy"
  args := tys[(.arr .num)]
  ret := (.arr .num)
  lam := .sync [⟨(.arr .num), false⟩] rfl
    (.seq (.ret (.builtin (.arrSort .num) args[.builtin (.arrConcat .num) args[var! 0, .builtin (.arrOf .num 0) args[]], .lam [] caps[] (.sync [⟨.num, false⟩, ⟨.num, false⟩] rfl
  (.seq (.ret (.prim (.numBin .sub) args[var! 0, var! 1]))
  .nil))]))
    .nil)

def mainBlock : Block TT [] .undef :=
  .nil

def program : Program TT where
  funs := [«sortedCopyDef»]
  globals := []
  main := mainBlock

/-! Call-unfolding lemmas: a call of a top-level function runs its body. -/

theorem «sortedCopy_call» (I : Impl) (vs : Vals TT [(.arr .num)]) :
    callFun I program «sortedCopyRef» vs = applyLam I program «sortedCopyDef».lam .nil vs := by
  rw [callFun.eq_1]; rfl

end New_b35u001

set_option maxHeartbeats 400000 in
theorem t_obs (I : Impl) (w : World Old_b35u001.TT) (a0 : Nat) (c0 : Array (Val Old_b35u001.TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some c0) (hn0 : a0 < w.next) (hs0 : c0.size < 2 ^ 32) :
    Obs.Equiv (Obs.ArrObs w.next)
      (JS.exec (callFun I Old_b35u001.program Old_b35u001.«sortedCopyRef» (.cons (.arr a0) .nil)) w)
      (JS.exec (callFun I New_b35u001.program New_b35u001.«sortedCopyRef» (.cons (.arr a0) .nil)) w) := by
  ts_destruct
  ts_cells
  all_goals (try ts_auto [Array.size_push, dtFreshRead])
  all_goals sorry

#print axioms t_obs
