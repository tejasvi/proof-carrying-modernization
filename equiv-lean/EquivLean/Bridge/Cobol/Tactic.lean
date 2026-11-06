import Cobol
import EquivLean.Bridge.Cobol.Attr
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Obs
import EquivLean.Bridge.Aeneas.Behaves

/-!
# Tactics of the COBOL bridge

* `equiv_cobol [h…]`: two COBOL runs (a same-language patch).  The goal
  `Equiv R (Cobol.run P₁ …) (Cobol.run P₂ …)` becomes a statement about the two results
  (`equiv_run_iff`), which coblean's symbolic executor evaluates; `cobol_grind` closes the
  leaves.
* `cobol_rust_equiv [h…]`: a COBOL run against Aeneas-translated Rust, in the weakest
  precondition form produced by `sim_exec_iff` (`wp rust (fun ot => obs ot = obs' cobolRun)`):
  `cobol_equiv` with the `cobol_aeneas` set added.  `cobol_aeneas` states Aeneas' checked
  `i64`/`i128` arithmetic, casts and binds as rewrite rules whose overflow tests are decided by
  coblean's interval arithmetic from the input ranges (`cobol_ranges`), so the Rust side is
  evaluated in the same `simp` pass as the COBOL side (`Demo/Cobol/AcctIntAeneas.lean`).

Range facts for the interval arithmetic must have the forms it reads: `x.natAbs < K`,
`Cobol.InRange lo hi x`, or one-sided bounds refining those.
-/

open Cobol
open Aeneas Aeneas.Std Result

namespace EquivLean.Cobol

/-! ## Aeneas' checked scalar operations as rewrite rules -/

theorem i128_bounds_iff (n : Int) :
    (-2 ^ (IScalarTy.I128.numBits - 1) ≤ n ∧ n < 2 ^ (IScalarTy.I128.numBits - 1)) ↔
      (-170141183460469231731687303715884105728 ≤ n ∧
        n < 170141183460469231731687303715884105728) := by
  simp only [IScalarTy.numBits]; constructor <;> intro h <;> omega

theorem i64_bounds_iff (n : Int) :
    (-2 ^ (IScalarTy.I64.numBits - 1) ≤ n ∧ n < 2 ^ (IScalarTy.I64.numBits - 1)) ↔
      (-9223372036854775808 ≤ n ∧ n < 9223372036854775808) := by
  simp only [IScalarTy.numBits]; constructor <;> intro h <;> omega

/-- A checked `i128` result: `ok` when it fits (decided by interval arithmetic during symbolic
execution), the overflow panic otherwise. -/
@[cobol_aeneas] theorem tryMk_I128 (n : Int) :
    IScalar.tryMk .I128 n =
      if h : -170141183460469231731687303715884105728 ≤ n ∧
          n < 170141183460469231731687303715884105728 then
        ok (IScalar.ofIntCore n ((i128_bounds_iff n).2 h))
      else fail .integerOverflow := by
  unfold IScalar.tryMk IScalar.tryMkOpt
  by_cases h : -170141183460469231731687303715884105728 ≤ n ∧
      n < 170141183460469231731687303715884105728
  · simp [IScalar.check_bounds, h, Result.ofOption]
  · simp [IScalar.check_bounds, h, Result.ofOption]

/-- A checked `i64` result. -/
@[cobol_aeneas] theorem tryMk_I64 (n : Int) :
    IScalar.tryMk .I64 n =
      if h : -9223372036854775808 ≤ n ∧ n < 9223372036854775808 then
        ok (IScalar.ofIntCore n ((i64_bounds_iff n).2 h))
      else fail .integerOverflow := by
  unfold IScalar.tryMk IScalar.tryMkOpt
  by_cases h : -9223372036854775808 ≤ n ∧ n < 9223372036854775808
  · simp [IScalar.check_bounds, h, Result.ofOption]
  · simp [IScalar.check_bounds, h, Result.ofOption]

@[cobol_aeneas] theorem mul_I128 (x y : I128) : x * y = IScalar.tryMk .I128 (x.val * y.val) := rfl
@[cobol_aeneas] theorem add_I128 (x y : I128) : x + y = IScalar.tryMk .I128 (x.val + y.val) := rfl
@[cobol_aeneas] theorem sub_I128 (x y : I128) : x - y = IScalar.tryMk .I128 (x.val - y.val) := rfl
@[cobol_aeneas] theorem neg_I128 (x : I128) : -. x = IScalar.tryMk .I128 (-x.val) := rfl
@[cobol_aeneas] theorem mul_I64 (x y : I64) : x * y = IScalar.tryMk .I64 (x.val * y.val) := rfl
@[cobol_aeneas] theorem add_I64 (x y : I64) : x + y = IScalar.tryMk .I64 (x.val + y.val) := rfl
@[cobol_aeneas] theorem sub_I64 (x y : I64) : x - y = IScalar.tryMk .I64 (x.val - y.val) := rfl
@[cobol_aeneas] theorem neg_I64 (x : I64) : -. x = IScalar.tryMk .I64 (-x.val) := rfl

/-- Signed `i128` division by a positive divisor truncates toward zero. -/
@[cobol_aeneas] theorem div_I128 (x y : I128) (hy : 0 < y.val) :
    x / y = ok (IScalar.ofIntCore (Int.tdiv x.val y.val)
      (EquivLean.Aeneas.IScalar.tdiv_bounds (by omega) (by omega))) := by
  have hv := EquivLean.Aeneas.IScalar.val_sdiv (x := x) (y := y) (by omega) (by omega)
  change IScalar.div x y = _
  unfold IScalar.div
  have h1 : (y.val != 0) = true := by simp; omega
  have h2 : ¬ ((x.val = IScalar.min .I128 && y.val = -1) = true) := by simp; omega
  rw [ite_eq_left h1, ite_eq_left h2]
  congr 1
  apply IScalar.eq_of_val_eq
  rw [hv, IScalar.ofInt_val_eq]

/-- Rust's `/` (`Int.tdiv`) as coblean's truncating division, which the interval arithmetic
and `omega` handle (inverse of `Rust.divRoundZ_truncation_eq_tdiv`). -/
@[cobol_aeneas] theorem tdiv_eq_divRoundZ (a b : Int) :
    Int.tdiv a b = Cobol.divRoundZ .truncation a b := (Rust.divRoundZ_truncation_eq_tdiv a b).symm

/-- `x as i128` for an `i64`. -/
@[cobol_aeneas] theorem cast_I128_of_I64 (x : I64) : (IScalar.cast .I128 x).val = x.val := by
  rw [IScalar.cast_val_eq]
  have := x.hBounds
  simp only [IScalarTy.numBits] at this ⊢
  apply Int.bmod_eq_of_le <;> first | omega | (simp; omega)

/-- `x as i128` for a `u16`. -/
@[cobol_aeneas] theorem hcast_I128_of_U16 (x : U16) :
    (UScalar.hcast .I128 x).val = (x.val : Int) := by
  rw [UScalar.hcast_val_eq]
  have := x.hBounds
  simp only [UScalarTy.numBits, IScalarTy.numBits] at this ⊢
  apply Int.bmod_eq_of_le <;> omega

/-- `x as i128` for a `u32`. -/
@[cobol_aeneas] theorem hcast_I128_of_U32 (x : U32) :
    (UScalar.hcast .I128 x).val = (x.val : Int) := by
  rw [UScalar.hcast_val_eq]
  have := x.hBounds
  simp only [UScalarTy.numBits, IScalarTy.numBits] at this ⊢
  apply Int.bmod_eq_of_le <;> omega

/-- `x as i64` for an `i128` that fits (the side conditions are decided by interval arithmetic
during symbolic execution). -/
@[cobol_aeneas] theorem cast_I64_of_I128 (x : I128) (h1 : -9223372036854775808 ≤ x.val)
    (h2 : x.val < 9223372036854775808) : (IScalar.cast .I64 x).val = x.val := by
  rw [IScalar.cast_val_eq]
  simp only [IScalarTy.numBits]
  apply Int.bmod_eq_of_le <;> first | omega | (simp; omega)

attribute [cobol_aeneas] bind_tc_ok Aeneas.Std.bind_ok IScalar.ofInt_val_eq IScalar.le_equiv
  IScalar.lt_equiv UScalar.le_equiv UScalar.lt_equiv UScalar.eq_equiv UScalar.ofNatCore_val_eq
  core.option.Option.unwrap_or lift GE.ge GT.gt
  EquivLean.Aeneas.wp_ok EquivLean.Aeneas.wp_fail EquivLean.Aeneas.wp_ite

/-! ## Tactics -/

/-- Two COBOL runs: `Equiv R (Cobol.run P₁ …) (Cobol.run P₂ …)` by evaluating both results
(`equiv_run_iff`, symbolic execution with the facts `h…`) and `cobol_grind`. -/
syntax "equiv_cobol" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| equiv_cobol) => `(tactic| equiv_cobol [])
  | `(tactic| equiv_cobol [$xs,*]) =>
    `(tactic| (rw [equiv_run_iff]; (try cobol_sym [ObsEq, sameFields_cons, sameFields_nil, $xs,*])
      <;> (try cobol_grind)))

/-- COBOL against Aeneas-translated Rust (weakest-precondition form): `cobol_equiv` with the
`cobol_aeneas` rewrite rules. -/
syntax "cobol_rust_equiv" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cobol_rust_equiv) => `(tactic| cobol_rust_equiv [])
  | `(tactic| cobol_rust_equiv [$xs,*]) => `(tactic| cobol_equiv [cobol_aeneas, $xs,*])

end EquivLean.Cobol
