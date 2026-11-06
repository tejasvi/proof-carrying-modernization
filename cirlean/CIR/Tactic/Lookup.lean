import Lean
import CIR.Semantics.Context

/-!
  Lookups in the module of a verification context (functions, records,
  globals by name), computed in meta code.

  Evaluating `List.find? (·.sym == s)` by `whnf` compares long mangled names
  character by character, nested, and exhausts the recursion limit on large
  modules. Here the list literal is walked and each key is reduced to a string
  literal and compared natively; the resulting equation is proved by `rfl`,
  checked by the kernel.
-/

namespace CIR.Tactic

open Lean Meta

/-- The elements of a list literal (the cells are unfolded by `whnfD`). -/
partial def listElems (e : Expr) : MetaM (Option (Array Expr)) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
    let e ← whnfD e
    match_expr e with
    | List.nil _ => return some acc
    | List.cons _ h t => go t (acc.push h)
    | _ => return none
  go e #[]

/-- `e` reduced to a string literal. -/
def strLit? (e : Expr) : MetaM (Option String) := do
  match ← whnfD e with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- Position and element of the first element of the list literal `xs` whose
key (`proj x`, a string) is `key`. `none` when there is none; failure when the
list or a key is not literal. -/
def findByKey (xs : Expr) (proj : Name) (key : String) : MetaM (Option (Option (Nat × Expr))) := do
  let some elems ← listElems xs | return none
  for i in [0:elems.size] do
    let some k ← strLit? (← mkAppM proj #[elems[i]!]) | return none
    if k == key then return some (some (i, elems[i]!))
  return some none

/-- The value of `M.findFunc? sym`, `M.findRecord? name`, `ctx.gaddr sym` or
`ctx.record? name` for a literal key, when it can be computed. -/
def lookupValue? (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  unless e.getAppNumArgs == 2 do return none
  let some key ← strLit? (e.getArg! 1) | return none
  let fn := e.getAppFn.constName?
  let mkOpt (ty : Expr) (r : Option Expr) : MetaM Expr :=
    match r with
    | some x => mkAppOptM ``Option.some #[ty, x]
    | none => mkAppOptM ``Option.none #[ty]
  match fn with
  | some ``CIR.Module.findFunc? =>
    let some r ← findByKey (← mkAppM ``CIR.Module.funcs #[e.getArg! 0]) ``CIR.FuncDecl.sym key | return none
    return some (← mkOpt (mkConst ``CIR.FuncDecl) (r.map (·.2)))
  | some ``CIR.Module.findRecord? =>
    let some r ← findByKey (← mkAppM ``CIR.Module.records #[e.getArg! 0]) ``CIR.RecordDecl.name key | return none
    return some (← mkOpt (mkConst ``CIR.RecordDecl) (r.map (·.2)))
  | some ``CIR.Module.findGlobal? =>
    let some r ← findByKey (← mkAppM ``CIR.Module.globals #[e.getArg! 0]) ``CIR.GlobalDecl.sym key | return none
    return some (← mkOpt (mkConst ``CIR.GlobalDecl) (r.map (·.2)))
  | some ``CIR.Ctx.record? =>
    let M ← mkAppM ``CIR.Ctx.mod #[e.getArg! 0]
    let some r ← findByKey (← mkAppM ``CIR.Module.records #[M]) ``CIR.RecordDecl.name key | return none
    return some (← mkOpt (mkConst ``CIR.RecordDecl) (r.map (·.2)))
  | some ``CIR.Ctx.gaddr =>
    -- only for contexts built by `Ctx.ofModule M` (global `i` is block `i`)
    let some c ← unfoldDefinition? (e.getArg! 0) | return none
    unless c.isAppOfArity ``CIR.Ctx.ofModule 1 do return none
    let some r ← findByKey (← mkAppM ``CIR.Module.globals #[c.getArg! 0]) ``CIR.GlobalDecl.sym key | return none
    return some (← mkOpt (mkConst ``Nat) (r.map fun (i, _) => mkNatLit i))
  | _ => return none

/-- `e = v` for the computed value `v` of a lookup `e`, by `rfl` (checked by
the kernel only). -/
def lookupEq? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some v ← lookupValue? e | return none
  let pf ← mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v)
  return some (v, pf)

end CIR.Tactic
