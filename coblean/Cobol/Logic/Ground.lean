/-
# Evaluating closed terms

`decodeNum` on literal bytes (storage initialised by `VALUE` clauses), CP037 conversions of
literal characters, …: closed terms are evaluated by the compiled code and replaced by the
resulting literal; the proof is `rfl`, so the kernel re-checks the value by evaluation (a
compiler bug cannot introduce an unsound step, only a failing proof).
-/
import Lean
import Cobol.Codec
import Cobol.Target.Codepage
import Cobol.Logic.Attr

namespace Cobol
open Lean Meta Simp

instance : ToExpr UInt8 where
  toExpr b := mkApp (mkConst ``UInt8.ofNat) (mkRawNatLit b.toNat)
  toTypeExpr := mkConst ``UInt8

/-- Evaluate a closed term of type `α` and return `e = value` by `rfl`. -/
def evalClosed (α : Type) [ToExpr α] (e : Expr) : SimpM Step := do
  if e.hasFVar || e.hasMVar then return .continue
  let ty := toTypeExpr α
  let v ← unsafe evalExpr α ty e
  let ve := toExpr v
  if ve == e then return .continue
  return .done { expr := ve, proof? := some (← mkEqRefl ve) }

/-- `decodeNum c f bs` on closed arguments. -/
simproc_decl reduceDecodeNum (decodeNum _ _ _) := fun e => evalClosed (Option Int) e

/-- `Codepage.cp037Char b` on a literal byte. -/
simproc_decl reduceCp037Char (Codepage.cp037Char _) := fun e => evalClosed Char e

/-- `Codepage.cp037Byte ch` on a literal character. -/
simproc_decl reduceCp037Byte (Codepage.cp037Byte _) := fun e => evalClosed (Option UInt8) e

/-- `Codepage.cp037Char b = ch` for a literal character `ch` ↦ `b = byte`. -/
simproc_decl reduceCp037CharEq ((Codepage.cp037Char _ : Char) = _) := fun e => do
  let_expr Eq _ lhs ch := e | return .continue
  let_expr Codepage.cp037Char b := lhs | return .continue
  if ch.hasFVar || ch.hasMVar then return .continue
  let some x ← unsafe evalExpr (Option UInt8) (toTypeExpr (Option UInt8))
      (mkApp (mkConst ``Codepage.cp037Byte) ch) | return .continue
  let xe := toExpr x
  let hx ← mkEqRefl (toExpr (some x))
  -- h : cp037Byte ch = some x  (checked by the kernel by evaluation)
  let h ← mkExpectedTypeHint hx (← mkEq (mkApp (mkConst ``Codepage.cp037Byte) ch) (toExpr (some x)))
  let iff := mkAppN (mkConst ``Codepage.cp037Char_eq_iff) #[b, ch, xe, h]
  let e' ← mkEq b xe
  return .done { expr := e', proof? := some (← mkPropExt iff) }

/-- `a = b` on closed `UInt8` terms (bytes of literals and of status codes), decided by
evaluation; the proof is `decide` checked by the kernel. -/
simproc_decl reduceUInt8Eq ((_ : UInt8) = _) := fun e => do
  let_expr Eq _ a b := e | return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let va ← unsafe evalExpr UInt8 (mkConst ``UInt8) a
  let vb ← unsafe evalExpr UInt8 (mkConst ``UInt8) b
  let inst ← synthInstance (mkApp (mkConst ``Decidable) e)
  if va == vb then
    let h := mkApp3 (mkConst ``of_decide_eq_true) e inst (← mkEqRefl (mkConst ``true))
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue h) }
  else
    let h := mkApp3 (mkConst ``of_decide_eq_false) e inst (← mkEqRefl (mkConst ``false))
    return .done { expr := mkConst ``False, proof? := some (← mkEqFalse h) }

/-- `compare a b` on integer literals (index loops: `SEARCH`, `PERFORM VARYING` an index). -/
simproc_decl reduceIntCompare (compare (_ : Int) _) := fun e => do
  let_expr compare _ _ a b := e | return .continue
  let some x ← getIntValue? a | return .continue
  let some y ← getIntValue? b | return .continue
  let r := mkConst (if x < y then ``Ordering.lt else if x == y then ``Ordering.eq else ``Ordering.gt)
  let pf ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)
  return .done { expr := r, proof? := some pf }

end Cobol
