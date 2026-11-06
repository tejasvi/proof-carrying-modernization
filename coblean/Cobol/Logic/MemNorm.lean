/-
# Memories as flat write chains

Symbolic execution represents storage as a chain of writes on the initial storage `m`:
`(m.write o₁ a₁).write o₂ a₂ …`.  Two things make chains grow with the number of statements:
a field written again (`ADD 1 TO CNT` in a loop body or a sequence of `IF`s) and the merge of
the two branches of an `IF`, which gives `if c then X else Y` with `X`, `Y` chains.  Reading a
field then walks the whole history, so straight-line code costs quadratic time.

Two simprocs keep a chain in a normal form with at most one write per field, in increasing
offset order (innermost first):

* `normWrite`: a new write moves below writes at higher disjoint offsets (`Mem.write_swap`)
  and replaces a write of the same field (`Mem.write_write_same`);
* `mergeMemIte`: `if c then X else Y` becomes one chain over the common part of `X` and `Y`,
  with value `if c then a else b` for every field written in either branch (the old value for
  a field written in one branch only), by `Mem.ite_write_write` / `ite_write_left` /
  `ite_write_right`, taking the higher offset first.

Reading a field then costs the number of distinct fields written, not the number of
statements executed.  Offsets must be literals and lengths must simplify to literals;
anything else is left alone (the rewrites are unconditional equalities or have literal side
conditions, so the normal form is only an optimisation).
-/
import Lean
import Cobol.Mem
import Cobol.Logic.Attr

namespace Cobol
open Lean Meta Simp

theorem Mem.write_swap_len (m : Mem) (o1 o2 : Nat) (a b : List UInt8) (n : Nat)
    (hb : b.length = n) (h : o2 + n ≤ o1) :
    (m.write o1 a).write o2 b = (m.write o2 b).write o1 a :=
  Mem.write_swap m o1 o2 a b (hb ▸ h)

theorem Mem.write_write_same_len (m : Mem) (o : Nat) (a b : List UInt8) (n : Nat)
    (ha : a.length = n) (hb : b.length = n) :
    (m.write o a).write o b = m.write o b :=
  Mem.write_write_same m o a b (ha.trans hb.symm)

/-- The length of a merged value (both branches have the field's length). -/
@[cobol_eval] theorem List.length_ite' {α : Type _} (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else b).length = if c then a.length else b.length := by split <;> rfl

/-- The length of a byte list as a literal, with a proof, by simplification. -/
def lenLit? (v : Lean.Expr) : SimpM (Option (Nat × Lean.Expr)) := do
  let e ← mkAppM ``List.length #[v]
  let r ← Simp.simp e
  let some n ← getNatValue? r.expr | return none
  return some (n, ← r.getProof)

/-- `m.write o v` as `(m, o, v)` with a literal offset. -/
def writeParts? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Nat × Lean.Expr × Lean.Expr)) := do
  let_expr Mem.write m o v := e | return none
  let some on ← getNatValue? o | return none
  return some (m, on, o, v)

/-- Insert the top write of a chain below writes at higher disjoint offsets; a write of the
same field (same offset, same length) is replaced. -/
simproc_decl normWrite (Mem.write _ _ _) := fun e => do
  let some (m, on, o, v) ← writeParts? e | return .continue
  let some (m', on', o', v') ← writeParts? m | return .continue
  if on == on' then
    let some (lv, hv) ← lenLit? v | return .continue
    let some (lv', hv') ← lenLit? v' | return .continue
    if lv != lv' then return .continue
    let pf ← mkAppM ``Mem.write_write_same_len #[m', o, v', v, mkNatLit lv, hv', hv]
    return .visit { expr := mkApp3 (mkConst ``Mem.write) m' o v, proof? := some pf }
  else if on < on' then
    let some (lv, hv) ← lenLit? v | return .continue
    unless on + lv ≤ on' do return .continue
    let hle ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (on + lv), o'])
    let hle ← mkExpectedTypeHint hle (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit lv], o'])
    let pf ← mkAppM ``Mem.write_swap_len #[m', o', o, v', v, mkNatLit lv, hv, hle]
    let e' := mkApp3 (mkConst ``Mem.write) (mkApp3 (mkConst ``Mem.write) m' o v) o' v'
    return .visit { expr := e', proof? := some pf }
  else
    return .continue

/-- `if c then X else Y` (memories) as one chain: returns the chain and a proof of
`(if c then X else Y) = chain`, or `none` when nothing can be pulled out. -/
partial def mergeMem (c inst x y : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if x == y then
    let pf ← mkAppOptM ``ite_self #[mkConst ``Mem, c, inst, x]
    return some (x, pf)
  let wx ← writeParts? x
  let wy ← writeParts? y
  -- one step: which write to pull out of the `if`
  let step : Option (Name × Array (Option Lean.Expr)) :=
    match wx, wy with
    | some (x', ox, oxe, a), some (y', oy, oye, b) =>
      if ox == oy then some (``Mem.ite_write_write, #[c, inst, x', y', oxe, a, b])
      else if ox > oy then some (``Mem.ite_write_left, #[c, inst, x', y, oxe, a])
      else some (``Mem.ite_write_right, #[c, inst, x, y', oye, b])
    | some (x', _, oxe, a), none => some (``Mem.ite_write_left, #[c, inst, x', y, oxe, a])
    | none, some (y', _, oye, b) => some (``Mem.ite_write_right, #[c, inst, x, y', oye, b])
    | none, none => none
  let some (thm, args) := step | return none
  let pf ← mkAppOptM thm args
  let some (_, _, rhs) := (← inferType pf).eq? | return none
  -- rhs = (if c then x₁ else y₁).write o v: continue with the inner `if`
  let_expr Mem.write inner o v := rhs | return none
  let_expr ite _ c' inst' x1 y1 := inner | return none
  match ← mergeMem c' inst' x1 y1 with
  | none => return some (rhs, pf)
  | some (r, p) =>
    let p' ← mkCongrFun (← mkCongrFun (← mkCongrArg (mkConst ``Mem.write) p) o) v
    return some (mkApp3 (mkConst ``Mem.write) r o v, ← mkEqTrans pf p')

/-- Merge the memories of the two branches of an `IF` into one chain. -/
simproc_decl mergeMemIte (@ite Mem _ _ _ _) := fun e => do
  let_expr ite ty c inst x y := e | return .continue
  unless ty.isConstOf ``Mem do return .continue
  let some (r, pf) ← mergeMem c inst x y | return .continue
  return .visit { expr := r, proof? := some pf }

end Cobol
