/-
# Deciding natural-number comparisons by `omega` during symbolic execution

A subscripted reference resolves to the offset `off + (k.toNat - 1) * stride`, and `MOVE` tests
whether sender and receiver overlap (`Sem.badOverlap`).  With a symbolic subscript `k` these
are linear comparisons of natural numbers whose truth follows from the bounds of `k` in the
context, but neither `simp` nor the interval simprocs of `Cobol.Logic.Bounds` (integers only)
decide them, and an undecided test makes symbolic execution explore both branches.

`omegaNatLt`, `omegaNatLe`, `omegaNatEq` and `omegaNatBEq` rewrite such a comparison to `True` /
`False` (or `true` / `false`) when `omega` proves it or its negation.  As in `Cobol.Logic.Bounds`,
only the hypotheses of the goal's own context are used (index below `lctxInitIndices`), never
the conditions of enclosing `if`s that simp adds while it works: simp caches its results across
those contexts.
-/
import Cobol
open Lean Meta Elab

namespace Cobol.StmCore

/-- Prove `p` by `omega` from the hypotheses of index `< maxIdx`. -/
def omegaProve? (p : Lean.Expr) (maxIdx : Nat) : MetaM (Option Lean.Expr) := do
  let lctx ← getLCtx
  let lctx' := lctx.foldl (init := lctx) fun acc d =>
    if d.index ≥ maxIdx then acc.erase d.fvarId else acc
  withLCtx lctx' (← getLocalInstances) do
    let mvar ← mkFreshExprMVar p
    try
      let gs ← Term.TermElabM.run' do
        Tactic.run mvar.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
      unless gs.isEmpty do return none
      let pr ← instantiateMVars mvar
      if pr.hasExprMVar then return none
      return some pr
    catch _ => return none

/-- `p` to `True` or `False` when `omega` decides it (only terms with free variables). -/
def omegaDecide (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  unless e.hasFVar do return .continue
  if e.hasExprMVar then return .continue
  let maxIdx := (← Simp.getContext).lctxInitIndices
  if let some pr ← omegaProve? e maxIdx then
    return .done { expr := mkConst ``True, proof? := some (← mkAppM ``eq_true #[pr]) }
  if let some pr ← omegaProve? (mkNot e) maxIdx then
    return .done { expr := mkConst ``False, proof? := some (← mkAppM ``eq_false #[pr]) }
  return .continue

simproc_decl omegaNatLt ((_ : Nat) < _) := fun e => omegaDecide e
simproc_decl omegaNatLe ((_ : Nat) ≤ _) := fun e => omegaDecide e
simproc_decl omegaNatEq ((_ : Nat) = _) := fun e => omegaDecide e

/-- An integer comparison that mentions a cast from `Nat` (a subscript bound `k ≤ ↑max`). -/
def hasNatCast (e : Lean.Expr) : Bool := (e.find? (·.isAppOf ``Nat.cast)).isSome

simproc_decl omegaIntLe ((_ : Int) ≤ _) := fun e =>
  if hasNatCast e then omegaDecide e else return .continue
simproc_decl omegaIntLt ((_ : Int) < _) := fun e =>
  if hasNatCast e then omegaDecide e else return .continue

theorem beq_of_eq_true {a b : Nat} (h : (a = b) = True) : (a == b) = true := by
  rw [of_eq_true h]; exact beq_self_eq_true b
theorem beq_of_eq_false {a b : Nat} (h : (a = b) = False) : (a == b) = false :=
  beq_false_of_ne (of_eq_false h)

/-- `a == b` on natural numbers, decided by `omega`. -/
simproc_decl omegaNatBEq ((_ : Nat) == _) := fun e => do
  let_expr BEq.beq _ _ a b := e | return .continue
  unless e.hasFVar do return .continue
  let p ← mkEq a b
  match ← omegaDecide p with
  | .done r =>
    if r.expr.isConstOf ``True then
      return .done { expr := mkConst ``Bool.true, proof? := some (← mkAppM ``beq_of_eq_true #[← r.getProof]) }
    else
      return .done { expr := mkConst ``Bool.false, proof? := some (← mkAppM ``beq_of_eq_false #[← r.getProof]) }
  | _ => return .continue

/-- A numeric literal cast from `Nat` to `Int` (a subscript's `max`): the interval simprocs of
`Cobol.Logic.Bounds` read only integer literals. -/
theorem natCast_ofNat_int (n : Nat) :
    ((OfNat.ofNat n : Nat) : Int) = (OfNat.ofNat n : Int) := rfl

end Cobol.StmCore
