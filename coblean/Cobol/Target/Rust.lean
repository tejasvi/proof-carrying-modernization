/-
# Rust target model

* Fixed-width integers are Lean's `Int32` / `Int64` / `UInt64` …: `wrapping_*` is plain
  `+ - *`; `checked_*` return `Option`; `/` and `%` truncate toward zero and panic on zero
  (`Except Panic`); arithmetic overflow in debug builds is a panic (`Rust.add` etc.).
  These are exactly the semantics of Rust's primitive integers, and `bv_decide` /
  `bv_omega` decide fixed-width goals over them.
* `Rust.Decimal` is the exact-arithmetic subset of `rust_decimal::Decimal` (96-bit
  mantissa, scale ≤ 28).  Every operation returns `none` outside that subset (overflow,
  scale above 28) instead of guessing rust_decimal's internal rescaling: a proof that a
  Rust function returns `some x` therefore never relies on unmodelled behaviour.
* `Rust.RoundingStrategy.*` are the COBOL rounding modes under rust_decimal's names.

Rust code can also be translated to Lean by Aeneas; its `Scalar` types correspond to the
integers here via `.val`.
-/
import Cobol.Sem.Arith
import Cobol.Logic.Attr

namespace Rust
open Cobol

/-- A Rust panic (arithmetic overflow in debug builds, division by zero, `unwrap` on `None`). -/
inductive Panic where
  | overflow | divByZero | unwrapNone
  deriving DecidableEq, Repr, Inhabited

/-! `rust_decimal::RoundingStrategy`. -/
namespace RoundingStrategy
abbrev MidpointNearestEven : Cobol.RoundingMode := .nearestEven
abbrev MidpointAwayFromZero : Cobol.RoundingMode := .nearestAwayFromZero
abbrev MidpointTowardZero : Cobol.RoundingMode := .nearestTowardZero
abbrev ToZero : Cobol.RoundingMode := .truncation
abbrev AwayFromZero : Cobol.RoundingMode := .awayFromZero
abbrev ToNegativeInfinity : Cobol.RoundingMode := .towardLesser
abbrev ToPositiveInfinity : Cobol.RoundingMode := .towardGreater
end RoundingStrategy

/-! ## `i64` -/

def i64Min : Int := -(2 ^ 63)
def i64Max : Int := 2 ^ 63 - 1

/-- `a.checked_add(b)`. -/
def checkedAdd (a b : Int64) : Option Int64 :=
  let r := a.toInt + b.toInt
  if i64Min ≤ r ∧ r ≤ i64Max then some (a + b) else none

/-- `a.checked_sub(b)`. -/
def checkedSub (a b : Int64) : Option Int64 :=
  let r := a.toInt - b.toInt
  if i64Min ≤ r ∧ r ≤ i64Max then some (a - b) else none

/-- `a.checked_mul(b)`. -/
def checkedMul (a b : Int64) : Option Int64 :=
  let r := a.toInt * b.toInt
  if i64Min ≤ r ∧ r ≤ i64Max then some (a * b) else none

/-- `a.checked_div(b)`: `None` on zero and on `MIN / -1`. -/
def checkedDiv (a b : Int64) : Option Int64 :=
  if b = 0 ∨ (a.toInt = i64Min ∧ b.toInt = -1) then none else some (a / b)

/-- `a.checked_rem(b)`. -/
def checkedRem (a b : Int64) : Option Int64 :=
  if b = 0 ∨ (a.toInt = i64Min ∧ b.toInt = -1) then none else some (a % b)

/-- `a + b` in a debug build (panics on overflow). -/
def add (a b : Int64) : Except Panic Int64 :=
  match checkedAdd a b with | some r => pure r | none => throw .overflow
def sub (a b : Int64) : Except Panic Int64 :=
  match checkedSub a b with | some r => pure r | none => throw .overflow
def mul (a b : Int64) : Except Panic Int64 :=
  match checkedMul a b with | some r => pure r | none => throw .overflow
def div (a b : Int64) : Except Panic Int64 :=
  if b = 0 then throw .divByZero else
  match checkedDiv a b with | some r => pure r | none => throw .overflow
def rem (a b : Int64) : Except Panic Int64 :=
  if b = 0 then throw .divByZero else
  match checkedRem a b with | some r => pure r | none => throw .overflow

/-! ## `i128` (values as `Int`)

Lean has no 128-bit integer type: an `i128` value is an `Int` in `[i128Min, i128Max]`, with
debug-build semantics (overflow panics).  Rust code that computes with `i128` intermediates
(scaled-integer money arithmetic) transcribes with these. -/

def i128Min : Int := -(2 ^ 127)
def i128Max : Int := 2 ^ 127 - 1

/-- `Ok r` if `r` is an `i128` value, else the overflow panic. -/
def fit128 (r : Int) : Except Panic Int :=
  if i128Min ≤ r ∧ r ≤ i128Max then .ok r else .error .overflow

def add128 (a b : Int) : Except Panic Int := fit128 (a + b)
def sub128 (a b : Int) : Except Panic Int := fit128 (a - b)
def mul128 (a b : Int) : Except Panic Int := fit128 (a * b)
def neg128 (a : Int) : Except Panic Int := fit128 (-a)
/-- `a.abs()` (panics on `i128::MIN`). -/
def abs128 (a : Int) : Except Panic Int := fit128 (a.natAbs : Int)
/-- `a / b`: truncation toward zero, panics on zero and on `i128::MIN / -1`. -/
def div128 (a b : Int) : Except Panic Int :=
  if b = 0 then .error .divByZero else fit128 (divRoundZ .truncation a b)

/-- Rust's `/` is `Int.tdiv` (truncation toward zero); `div128` states it with `divRoundZ`, which
symbolic execution and `omega` handle. -/
theorem divRoundZ_truncation_eq_tdiv (a b : Int) : divRoundZ .truncation a b = a.tdiv b := by
  unfold divRoundZ divRound
  by_cases hb : b < 0
  · simp only [hb, ↓reduceIte]
    by_cases ha : 0 ≤ -a
    · simp only [ha, ↓reduceIte]
      rw [← Int.tdiv_eq_ediv_of_nonneg ha, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg]
    · simp only [ha, ↓reduceIte, Int.neg_neg]
      rw [← Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ a by omega), ← Int.tdiv_neg, Int.neg_neg]
  · simp only [hb, ↓reduceIte]
    by_cases ha : 0 ≤ a
    · simp only [ha, ↓reduceIte, Int.tdiv_eq_ediv_of_nonneg ha]
    · simp only [ha, ↓reduceIte]
      rw [← Int.tdiv_eq_ediv_of_nonneg (show 0 ≤ -a by omega), Int.neg_tdiv, Int.neg_neg]

/-- The usual Rust idiom for "divide, rounding half away from zero" on integers,
`if n >= 0 { (2*n + d) / (2*d) } else { -((2*-n + d) / (2*d)) }` (`d > 0`), is
`divRound .nearestAwayFromZero`.  Stated left to right for symbolic execution: the transcribed
Rust folds back to the rounding of the COBOL / Java side (`d2` is `2 * d` as a literal). -/
theorem divRound_halfUp_idiom (n d d2 : Int) (hd : 0 < d) (h2 : d2 = 2 * d) :
    (if 0 ≤ n then divRound .truncation (2 * n + d) d2
      else -divRound .truncation (2 * -n + d) d2) = divRound .nearestAwayFromZero n d := by
  subst h2
  simp only [divRound]
  by_cases hn : 0 ≤ n
  · simp only [hn, ↓reduceIte, show 0 ≤ 2 * n + d by omega]
  · simp only [hn, ↓reduceIte, show 0 ≤ 2 * -n + d by omega]

/-! ## `rust_decimal::Decimal` (exact subset) -/

/-- Mantissa bound `2^96`. -/
def decMantMax : Int := 2 ^ 96

/-- `rust_decimal::Decimal`: value `mantissa * 10^(-scale)`, `|mantissa| < 2^96`,
`scale ≤ 28`. -/
structure Decimal where
  mantissa : Int
  scale : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

/-- Inside the representable range. -/
def ok (m : Int) (s : Nat) : Bool := m.natAbs < 2 ^ 96 && s ≤ 28

/-- `Decimal::new(m, s)` (`none` if not representable). -/
def new (m : Int) (s : Nat) : Option Decimal := if ok m s then some ⟨m, s⟩ else none

/-- `a.checked_add(b)` on the exact subset. -/
def checkedAdd (a b : Decimal) : Option Decimal :=
  let s := max a.scale b.scale
  new (Sem.align a.mantissa a.scale s + Sem.align b.mantissa b.scale s) s

/-- `a.checked_sub(b)` on the exact subset. -/
def checkedSub (a b : Decimal) : Option Decimal :=
  let s := max a.scale b.scale
  new (Sem.align a.mantissa a.scale s - Sem.align b.mantissa b.scale s) s

/-- `a.checked_mul(b)` on the exact subset (product scale must stay ≤ 28). -/
def checkedMul (a b : Decimal) : Option Decimal :=
  new (a.mantissa * b.mantissa) (a.scale + b.scale)

/-- `a.round_dp_with_strategy(dp, strategy)`. -/
def roundDp (a : Decimal) (dp : Nat) (m : Cobol.RoundingMode) : Decimal :=
  if dp < a.scale then ⟨divRound m a.mantissa (10 ^ (a.scale - dp)), dp⟩ else a

/-- `a.rescale(s)` (mutating in Rust): round to `s` decimal places (midpoint away from zero)
or pad with zeros. -/
def rescale (a : Decimal) (s : Nat) : Option Decimal :=
  new (Cobol.rescale .nearestAwayFromZero a.mantissa a.scale s) s

/-- Exact quotient rounded to `s` places (as `(a / b).round_dp_with_strategy(s, m)` computes
when the true quotient needs at most 28 places; otherwise rust_decimal has already rounded
and the model returns `none`). -/
def divRoundDp (a b : Decimal) (s : Nat) (m : Cobol.RoundingMode) : Option Decimal :=
  if b.mantissa = 0 then none
  else if Sem.quotExact a.mantissa a.scale b.mantissa b.scale 28 then
    new (Sem.quot m a.mantissa a.scale b.mantissa b.scale s) s
  else none

/-- Numeric value at scale `s` (exact when `s ≥ scale`). -/
def valueAt (a : Decimal) (s : Int) : Int := Cobol.rescale .truncation a.mantissa a.scale s

end Decimal

/-- Conversions of merged values go into the `if` (where `as i64` of a value that fits
disappears, `reduceInt64ToIntOfInt`). -/
theorem int64_toInt_ite (c : Prop) [Decidable c] (a b : Int64) :
    (if c then a else b).toInt = if c then a.toInt else b.toInt := by split <;> rfl

/-- `u16` / `u32` equality is equality of the values. -/
theorem uint16_eq_iff (a b : UInt16) : (a = b) = (a.toNat = b.toNat) := propext UInt16.toNat_inj.symm

attribute [rust_eval] int64_toInt_ite uint16_eq_iff UInt16.toNat_zero Int64.toInt_zero Int64.ofInt_toInt
  i128Min i128Max fit128 add128 sub128 mul128 neg128 abs128 div128
  i64Min i64Max checkedAdd checkedSub checkedMul checkedDiv checkedRem
  add sub mul div rem Decimal.ok Decimal.new Decimal.checkedAdd Decimal.checkedSub
  Decimal.checkedMul Decimal.roundDp Decimal.rescale Decimal.divRoundDp Decimal.valueAt

end Rust
