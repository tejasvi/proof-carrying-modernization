/-
StrictTS proof layer: tactics.

* `ts_sym [h, …]` — symbolic execution of concrete IR on a symbolic world (the `ts_sym`
  simp set plus `simp`'s defaults and the given facts), followed by peeling
  `some (.ok (v, w)) = some (.ok (v', w'))` into `v = v' ∧ w = w'`.
* `ts_safe` — discharges `F64.Safe n` side conditions (|n| ≤ 2^53) for sums of int32/uint32
  terms by bit-vector arithmetic (`bv_omega`).
* `ts_int32` — normalises int32 idioms on `number` (`| 0`, `>>> 0`, `^`, `&`, `|`, `<<`, `>>`,
  `>>>`, `Math.imul`, `+`/`-` of int32 values) into `BitVec 32` and closes the goal with
  `bv_decide`.
-/
import StrictTS.Proof.Arrays
import StrictTS.Proof.Maps
import StrictTS.Num.F64Lemmas
import StrictTS.Proof.Numbers

namespace StrictTS

/-- Symbolic execution with the `ts_sym` simp set. -/
syntax (name := tsSym) "ts_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ts_sym) =>
    `(tactic| simp only [ts_sym, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, and_true, true_and])
  | `(tactic| ts_sym [$hs,*]) =>
    `(tactic| simp only [ts_sym, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, and_true, true_and, $hs,*])

/-- Discharger for exact-integer side conditions of the number bridge. -/
macro "ts_safe" : tactic =>
  `(tactic| (simp only [F64.Safe, BitVec.toInt_eq_toNat_cond]; bv_omega))

/-- Int32 normal form, then `bv_decide`. -/
macro "ts_int32" : tactic => `(tactic| (
  simp only [Val.num.injEq, F64.bxor, F64.bor, F64.band, F64.bnot, F64.shr, F64.shl, F64.sar, F64.imul,
    F64.ofNat_eq_ofInt, F64.toInt32_ofInt32, F64.toInt32_ofUint32]
  simp (disch := ts_safe) only [F64.toInt32_ofInt]
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.zero_mod,
    BitVec.ushiftRight_zero, F64.ofUint32_eq, F64.ofInt32_eq]
  simp (disch := ts_safe) only [F64.add_ofInt, F64.sub_ofInt, F64.toInt32_ofInt]
  simp (disch := ts_safe) only [F64.ofInt_inj_iff, Int.ofNat_inj, BitVec.toNat_inj, Int.cast_ofNat_Int]
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  bv_decide))

open Lean Elab Tactic Meta in
/-- `ts_forof xs using Inv` finds the `for (const x of arr)` loop `exec (evalForOf I P a i body env) w`
in the goal, applies `evalForOf_inv` with the array contents `xs` and the index invariant `Inv`,
and replaces the loop's execution by its result `some (.ok (.normal, env'), w')`, adding the
hypothesis `hinv : Inv xs.size env' w'`. Remaining goals: `cell` (the invariant keeps the array),
`step` (one iteration preserves it) and `init`. -/
elab "ts_forof " xs:term " using " inv:term : tactic => withMainContext do
  let goal ← getMainTarget
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalForOf)
    | throwError "ts_forof: no `for … of` loop (evalForOf) in the goal"
  let loop := e.getArg! 2
  let w := e.getArg! 3
  let args := loop.getAppArgs
  -- evalForOf {TT} I P {Γ} {ρ} {t} a i body env
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let a ← Term.exprToSyntax args[6]!
  let i ← Term.exprToSyntax args[7]!
  let body ← Term.exprToSyntax args[8]!
  let env ← Term.exprToSyntax args[9]!
  let ws ← Term.exprToSyntax w
  evalTactic (← `(tactic|
    have hloop := StrictTS.evalForOf_inv $I $P $body $a $xs $inv ?cell ?step
      (($xs).size - $i) $i $env $ws rfl (by omega) ?init))
  let envI := mkIdent `env'
  let wI := mkIdent `w'
  let hrunI := mkIdent `hrun
  let hinvI := mkIdent `hinv
  evalTactic (← `(tactic| obtain ⟨$envI, $wI, $hrunI, $hinvI⟩ := hloop))
  evalTactic (← `(tactic| rw [$hrunI:ident]))

open Lean Elab Tactic Meta in
/-- `ts_while Inv, V, Post` finds the loop `exec (evalLoop I P c body step env) w` (a `while`
or counted `for`) in the goal, applies `evalLoop_inv` with invariant `Inv`, variant `V` and
exit condition `Post`, and replaces the loop's execution by its result, adding
`hpost : Post env' w'`. Remaining goals: `step` (one iteration, in weakest-precondition form)
and `init`. -/
elab "ts_while " inv:term ", " var:term ", " post:term : tactic => withMainContext do
  let goal ← getMainTarget
  let some e := goal.find? (fun e => e.isAppOfArity ``JS.exec 4 && (e.getArg! 2).isAppOf ``evalLoop)
    | throwError "ts_while: no loop (evalLoop) in the goal"
  let loop := e.getArg! 2
  let args := loop.getAppArgs
  -- evalLoop {TT} I P {Γ} {ρ} c body step env
  let I ← Term.exprToSyntax args[1]!
  let P ← Term.exprToSyntax args[2]!
  let c ← Term.exprToSyntax args[5]!
  let body ← Term.exprToSyntax args[6]!
  let step ← Term.exprToSyntax args[7]!
  let env ← Term.exprToSyntax args[8]!
  let ws ← Term.exprToSyntax (e.getArg! 3)
  evalTactic (← `(tactic|
    have hloop := StrictTS.evalLoop_inv $I $P $c $body $step $inv $post $var ?step
      ($var $env $ws) $env $ws rfl ?init))
  let envI := mkIdent `env'
  let wI := mkIdent `w'
  let hrunI := mkIdent `hrun
  let hpostI := mkIdent `hpost
  evalTactic (← `(tactic| obtain ⟨$envI, $wI, $hrunI, $hpostI⟩ := hloop))
  evalTactic (← `(tactic| rw [$hrunI:ident]))

end StrictTS
