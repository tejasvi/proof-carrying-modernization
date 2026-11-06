import Lean
import CIR.Logic.Native

/-!
  Test theorems checked by the kernel.

  `evalIter ctx n` is the `n`-th approximation of the interpreter: `n` steps of
  the functional whose least fixpoint defines `evalOps`, ..., `evalCall`
  (extracted from `evalOps.mutual`), starting from the everywhere-`div`
  functions. Every approximation is below the fixpoint in the flat order, so
  an `ok` result of an approximation is the result of the interpreter
  (`callReturnsK_sound`). The approximation is structural recursion on `n`,
  which the kernel evaluates: `cir_kernel` proves a test theorem by
  `decide +kernel`, with no axiom beyond the standard ones.
-/

open Lean Meta Elab Command

namespace CIR

/-- The everywhere-`div` value of a tuple type of interpreter functions. -/
partial def mkDivTuple (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``PProd 2 then
    return ← mkAppM ``PProd.mk #[← mkDivTuple (ty.getArg! 0), ← mkDivTuple (ty.getArg! 1)]
  if ty.isForall then
    return ← forallBoundedTelescope ty (some 1) fun xs b => do mkLambdaFVars xs (← mkDivTuple b)
  if ty.isAppOfArity ``Res 1 then
    return mkApp (mkConst ``Res.div) (ty.getArg! 0)
  throwError "mkDivTuple: unexpected type {ty}"

run_meta do
  let info ← getConstInfo ``CIR.evalOps.mutual
  let (tupTy, inst, F, hmono, divT) ← lambdaTelescope info.value! fun xs body => do
    let args := body.getAppArgs
    -- the tuple type and its order do not depend on the context
    if args[0]!.containsFVar xs[0]!.fvarId! || args[1]!.containsFVar xs[0]!.fvarId! then
      throwError "evalOps.mutual: the tuple type depends on the context"
    let tupTy := args[0]!
    let inst := args[1]!
    let F ← mkLambdaFVars xs args[2]!
    let hmono ← mkLambdaFVars xs args[3]!
    let divT ← mkLambdaFVars xs (← mkDivTuple args[0]!)
    return (tupTy, inst, F, hmono, divT)
  let ctxTy := mkConst ``CIR.Ctx
  addAndCompile <| .defnDecl {
    name := `CIR.EvalTuple, levelParams := [], type := ← inferType tupTy, value := tupTy,
    hints := .abbrev, safety := .safe }
  addDecl <| .defnDecl {
    name := `CIR.evalTupleCCPO, levelParams := [], type := ← inferType inst, value := inst,
    hints := .abbrev, safety := .safe }
  addAndCompile <| .defnDecl {
    name := `CIR.evalFunctional, levelParams := [], type := ← inferType F, value := F,
    hints := .abbrev, safety := .safe }
  addAndCompile <| .defnDecl {
    name := `CIR.evalDiv, levelParams := [], type := ← inferType divT, value := divT,
    hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl {
    name := `CIR.evalFunctional_mono, levelParams := [], type := ← inferType hmono, value := hmono }
  let _ := ctxTy

attribute [reducible] EvalTuple evalDiv evalFunctional
attribute [instance_reducible] evalTupleCCPO
attribute [instance] evalTupleCCPO

/-- The `n`-th approximation of the interpreter. -/
def evalIter (ctx : Ctx) : Nat → EvalTuple
  | 0 => evalDiv ctx
  | n + 1 => evalFunctional ctx (evalIter ctx n)

theorem evalDiv_le (ctx : Ctx) (t : EvalTuple) : Lean.Order.PartialOrder.rel (evalDiv ctx) t := by
  repeat' first
    | exact Lean.Order.FlatOrder.rel.bot
    | (constructor)
    | (intro)

theorem evalIter_le (ctx : Ctx) (n : Nat) :
    Lean.Order.PartialOrder.rel (evalIter ctx n) (evalOps.mutual ctx) := by
  induction n with
  | zero => exact evalDiv_le ctx _
  | succ n ih =>
    show Lean.Order.PartialOrder.rel (evalFunctional ctx (evalIter ctx n)) (evalOps.mutual ctx)
    rw [show evalOps.mutual ctx = evalFunctional ctx (evalOps.mutual ctx) from
      Lean.Order.fix_eq (evalFunctional_mono ctx)]
    exact evalFunctional_mono ctx _ _ ih

/-- The call, by the `n`-th approximation. -/
abbrev evalCallIter (ctx : Ctx) (n : Nat) : String → List Val → Mem → Res (Exit × Mem) :=
  (evalIter ctx n).2.2.2.2.2.2.2.2.2.2.2

theorem flat_ok {α : Type} {x y : Res α} {r : α}
    (h : Lean.Order.PartialOrder.rel x y) (hx : x = .ok r) : y = .ok r := by
  cases h with
  | bot => cases hx
  | refl => exact hx

theorem evalCallIter_sound {ctx : Ctx} {n : Nat} {sym : String} {args : List Val} {m : Mem}
    {r : Exit × Mem} (h : evalCallIter ctx n sym args m = .ok r) : evalCall ctx sym args m = .ok r := by
  have hle := (evalIter_le ctx n).2.2.2.2.2.2.2.2.2.2.2 sym args m
  have e : evalCall ctx sym args m = (evalOps.mutual ctx).2.2.2.2.2.2.2.2.2.2.2 sym args m := by
    with_unfolding_all rfl
  rw [e]
  exact flat_ok hle h

/-- The call (within `n` approximation steps) returns normally, with a value
passing the test `p`. -/
def callReturnsK (n : Nat) (ctx : Ctx) (sym : String) (args : List Val) (m : Mem)
    (p : Option Val → Bool) : Bool :=
  match evalCallIter ctx n sym args m with
  | .ok (.ret v, _) => p v
  | _ => false

theorem callReturnsB_of_callReturnsK {n : Nat} {ctx : Ctx} {sym : String} {args : List Val}
    {m : Mem} {p : Option Val → Bool} (h : callReturnsK n ctx sym args m p = true) :
    callReturnsB ctx sym args m p = true := by
  unfold callReturnsK at h
  unfold callReturnsB
  split at h
  · rename_i v m' heq
    rw [evalCallIter_sound heq]; exact h
  · exact absurd h Bool.false_ne_true

theorem returns_int_of_callReturnsK {n : Nat} {ctx : Ctx} {sym : String} {args : List Val}
    {m : Mem} {k : Int} (h : callReturnsK n ctx sym args m (isInt k) = true) :
    Returns ctx sym args m (fun v _ => v = some (.int k)) :=
  returns_int_of_callReturnsB (callReturnsB_of_callReturnsK h)

end CIR

/-- `cir_kernel` proves `Returns ctx sym args m (fun v _ => v = some (.int k))`
for a concrete call by kernel evaluation of the interpreter (at most 10^9
approximation steps; standard axioms only). -/
macro "cir_kernel" : tactic =>
  `(tactic| (apply CIR.returns_int_of_callReturnsK (n := 1000000000); decide +kernel))
