/-
# Distributing `match` over `if`

`match (if c then a else b), … with alts` ↦ `if c then (match a, … with alts)
else (match b, … with alts)` for matchers whose motive does not depend on the
discriminants.

Symbolic execution produces a data-dependent `if` wherever control depends on symbolic data.
Without this simproc the `match` that consumes the result would be stuck, and simp would
then simplify all its arms on symbolic arguments (each arm being "the rest of the program").
With it, each branch gets a concrete scrutinee and only the selected arm is evaluated, so
symbolic execution yields a tree of `if`s with fully evaluated leaves.
-/
import Lean
import Cobol.Logic.Attr

namespace Cobol
open Lean Meta Simp

/-- The motive `fun x₁ … xₙ => T` ignores its arguments. -/
private def constMotive (motive : Expr) (n : Nat) : Bool :=
  go motive n
where
  go : Expr → Nat → Bool
    | .lam _ _ body _, k + 1 => go body k
    | body, 0 => !body.hasLooseBVars
    | _, _ => false

/-- Distribute a non-dependent `match` over an `if` / `ite` scrutinee. -/
simproc_decl matchIte (_) := fun e => do
  let some app ← matchMatcherApp? e | return .continue
  if !constMotive app.motive app.discrs.size then return .continue
  -- find a discriminant that is an `ite`
  let some i := app.discrs.findIdx? (fun d => d.consumeMData.isAppOfArity ``ite 5)
    | return .continue
  let d := app.discrs[i]!.consumeMData
  let α := d.getArg! 0
  let c := d.getArg! 1
  let inst := d.getArg! 2
  let a := d.getArg! 3
  let b := d.getArg! 4
  -- f := fun x => match …, x, … with alts
  let f ← withLocalDeclD `x α fun x => do
    let app' := { app with discrs := app.discrs.set! i x, remaining := #[] }
    mkLambdaFVars #[x] app'.toExpr
  let β ← inferType (mkAppN e #[]) -- type of the match (without `remaining`)
  let _ := β
  let fa := f.beta #[a]
  let fb := f.beta #[b]
  let resTy ← inferType fa
  let u ← getLevel resTy
  let v ← getLevel α
  let e' := mkAppN (mkConst ``ite [u]) #[resTy, c, inst, fa, fb]
  let proof := mkAppN (mkConst ``apply_ite [v, u]) #[α, resTy, f, c, inst, a, b]
  -- re-apply arguments beyond the matcher (`remaining`), if any
  if app.remaining.isEmpty then
    return .visit { expr := e', proof? := some proof }
  else
    return .continue

/-- Pre-simproc version: simplify the discriminants first (with the full simplifier), and
if one becomes an `if`, distribute immediately, so the arms of the `match` are never
simplified on a symbolic discriminant. -/
simproc_decl matchItePre (_) := fun e => do
  let some app ← matchMatcherApp? e | return .continue
  if !app.remaining.isEmpty then return .continue
  if !constMotive app.motive app.discrs.size then return .continue
  for i in [0:app.discrs.size] do
    let d := app.discrs[i]!
    let r ← Simp.simp d
    let d' := r.expr.consumeMData
    if d'.isAppOfArity ``ite 5 then
      let α := d'.getArg! 0
      let c := d'.getArg! 1
      let inst := d'.getArg! 2
      let a := d'.getArg! 3
      let b := d'.getArg! 4
      let f ← withLocalDeclD `x α fun x => do
        let app' := { app with discrs := app.discrs.set! i x }
        mkLambdaFVars #[x] app'.toExpr
      let fa := f.beta #[a]
      let fb := f.beta #[b]
      let resTy ← inferType fa
      let u ← getLevel resTy
      let v ← getLevel α
      let e' := mkAppN (mkConst ``ite [u]) #[resTy, c, inst, fa, fb]
      let p2 := mkAppN (mkConst ``apply_ite [v, u]) #[α, resTy, f, c, inst, a, b]
      let proof ← match r.proof? with
        | none => pure p2
        | some h => do
          let p1 ← Lean.Meta.mkCongrArg f h
          mkEqTrans p1 p2
      return .visit { expr := e', proof? := some proof }
  return .continue

/-- A (simplified) term that only a loop result can make progress on: a folded loop, or a
`match` left stuck on one. -/
partial def stuckOnLoop (d : Lean.Expr) : MetaM Bool := do
  let d := d.consumeMData
  if d.isAppOf `Cobol.Sem.loopUntil then return true
  let some app ← matchMatcherApp? d | return false
  app.discrs.anyM stuckOnLoop

/-- Do not explore the alternatives of a `match` on the result of a folded loop (or on a
`match` that is itself stopped there): simplify the discriminants only, then stop. -/
simproc_decl stopAtLoop (_) := fun e => do
  let some app ← matchMatcherApp? e | return .continue
  if !app.remaining.isEmpty then return .continue
  let rs ← app.discrs.mapM fun d => Simp.simp d
  unless ← rs.anyM fun r => stuckOnLoop r.expr do return .continue
  let mut cur := app
  let mut proof : Option Lean.Expr := none
  for h : i in [0:rs.size] do
    let r := rs[i]
    if let some hr := r.proof? then
      let c := cur
      let f ← withLocalDeclD `x (← inferType app.discrs[i]!) fun x =>
        mkLambdaFVars #[x] { c with discrs := c.discrs.set! i x }.toExpr
      let step ← Lean.Meta.mkCongrArg f hr
      proof ← match proof with
        | none => pure (some step)
        | some p => some <$> mkEqTrans p step
    cur := { cur with discrs := cur.discrs.set! i r.expr }
  return .done { expr := cur.toExpr, proof? := proof }

end Cobol
