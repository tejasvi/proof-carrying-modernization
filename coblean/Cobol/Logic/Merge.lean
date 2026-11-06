/-
# Merging `if`s of constructor applications

State merging (see `Cobol.Logic.Eval`) needs two generic rewrites, for any inductive type:

* `mergeCtorIte`: `if c then K a₁ … aₙ else K b₁ … bₙ  ↦  K (if c then a₁ else b₁) …`
  for one constructor `K` (structures: states, records, `BigDecimal`s, pairs; `some`; `.ok`);
  equal fields stay as they are.  Results `Signal × State` are excluded: a `match` on the
  signal needs the `if` on top (`matchItePre` distributes it); those merge only when the
  signals agree (`Prod.ite_mk_same_fst`).
* `projIte`: `(if c then a else b).f  ↦  if c then a.f else b.f` for structure projections.

The proof of a merge is `Decidable.casesOn` on the instance of the `if`, with `rfl` in both
cases (an `if` on `isTrue h` / `isFalse h` reduces to its branch), checked by the kernel.
-/
import Lean
import Cobol.IR

namespace Cobol
open Lean Meta Simp

theorem ite_app.{u, v} {α : Sort u} {β : Sort v} (c : Prop) [Decidable c] (f g : α → β) (x y : α) :
    (if c then f x else g y) = (if c then f else g) (if c then x else y) := by
  split <;> rfl

/-- The constructor at the head of `e` (applied to at least its parameters and one field). -/
private def ctorHead? (e : Lean.Expr) : MetaM (Option ConstructorVal) := do
  let .const n _ := e.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? n | return none
  if e.getAppNumArgs ≤ ci.numParams then return none
  return some ci

/-- Merge an `if` whose branches apply the same constructor, one field at a time:
`if c then K … x else K … y ↦ (if c then K … else K …) (if c then x else y)`; simp repeats
on the head until `ite_self` closes it, and on the fields (`ite_self` again where equal). -/
simproc_decl mergeCtorIte (ite _ _ _) := fun e => do
  let_expr ite ty c inst a b := e | return .continue
  let some ka ← ctorHead? a | return .continue
  -- control results (`Sem.Res` is an abbreviation of `Signal × State`) are not merged
  let ty' ← whnfR ty
  if ty'.isConstOf ``Signal then return .continue
  if ty'.isAppOfArity ``Prod 2 then
    -- (`←` inside an `&&` would run unconditionally)
    if (← whnfR (ty'.getArg! 0)).isConstOf ``Signal then return .continue
  let some kb ← ctorHead? b | return .continue
  if ka.name != kb.name || a.getAppNumArgs != b.getAppNumArgs then return .continue
  let .app f x := a | return .continue
  let .app g y := b | return .continue
  let fty ← whnfR (← inferType f)
  let .forallE _ α β _ := fty | return .continue
  if β.hasLooseBVars then return .continue  -- dependent field
  unless ← isDefEq fty (← inferType g) do return .continue
  let u ← getLevel α
  let v ← getLevel β
  let fg := mkApp5 (.const ``ite [mkLevelIMax' u v]) fty c inst f g
  let xy := mkApp5 (.const ``ite [u]) α c inst x y
  let pf := mkAppN (.const ``Cobol.ite_app [u, v]) #[α, β, c, inst, f, g, x, y]
  return .visit { expr := mkApp fg xy, proof? := some pf }

/-- `(if c then a else b).f = if c then a.f else b.f` for a structure projection `f`. -/
simproc_decl projIte (_) := fun e => do
  match e with
  | .proj s i x =>
    let_expr ite _ c inst a b := x | return .continue
    let ty ← inferType e
    let f ← withLocalDeclD `x (← inferType x) fun y => mkLambdaFVars #[y] (Lean.Expr.proj s i y)
    let e' ← mkAppOptM ``ite #[ty, c, inst, Lean.Expr.proj s i a, Lean.Expr.proj s i b]
    let pf ← mkAppOptM ``apply_ite #[none, none, f, c, inst, a, b]
    return .visit { expr := e', proof? := some pf }
  | .app fn x =>
    let .const n _ := fn.getAppFn | return .continue
    let some info ← getProjectionFnInfo? n | return .continue
    if fn.getAppNumArgs != info.numParams then return .continue
    let_expr ite _ c inst a b := x | return .continue
    let ty ← inferType e
    let e' ← mkAppOptM ``ite #[ty, c, inst, mkApp fn a, mkApp fn b]
    let pf ← mkAppOptM ``apply_ite #[none, none, fn, c, inst, a, b]
    return .visit { expr := e', proof? := some pf }
  | _ => return .continue

end Cobol
