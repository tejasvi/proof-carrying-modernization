/-
Copyright (c) 2026. All rights reserved.

# Exact scaled-integer rounding

COBOL fixed-point values are modelled as scaled integers: a value `v : Int` at scale `s`
denotes the rational `v * 10^(-s)`.  Every place where COBOL drops low-order digits
(`ROUNDED`, truncation on store, intermediate precision of division) goes through
`divRound`, the single rounding primitive of this library.

The eight rounding modes are the COBOL 2014 `ROUNDED MODE` modes.  They correspond 1-1 to
`java.math.RoundingMode` and to `rust_decimal::RoundingStrategy`, which is what makes
COBOL / Java / Rust equivalence proofs mostly definitional: all three models call the same
`divRound`.

`divRound` is written with `Int` Euclidean division (`/`, `%`) and `if` only, so that after
unfolding, goals with literal divisors (the usual `10^k`) are decided by `omega`.
-/

namespace Cobol

/-- Rounding modes (COBOL `ROUNDED MODE IS ...`).  Java / Rust names in the comments. -/
inductive RoundingMode where
  /-- `AWAY-FROM-ZERO`; Java `UP`; Rust `AwayFromZero`. -/
  | awayFromZero
  /-- `NEAREST-AWAY-FROM-ZERO` (the meaning of a plain `ROUNDED`); Java `HALF_UP`;
  Rust `MidpointAwayFromZero`. -/
  | nearestAwayFromZero
  /-- `NEAREST-EVEN`; Java `HALF_EVEN`; Rust `MidpointNearestEven`. -/
  | nearestEven
  /-- `NEAREST-TOWARD-ZERO`; Java `HALF_DOWN`; Rust `MidpointTowardZero`. -/
  | nearestTowardZero
  /-- `TOWARD-GREATER`; Java `CEILING`; Rust `ToPositiveInfinity`. -/
  | towardGreater
  /-- `TOWARD-LESSER`; Java `FLOOR`; Rust `ToNegativeInfinity`. -/
  | towardLesser
  /-- `TRUNCATION` (no `ROUNDED` phrase); Java `DOWN`; Rust `ToZero`. -/
  | truncation
  /-- `PROHIBITED`: inexact results are a size error; Java `UNNECESSARY`.
  `divRound` truncates; inexactness is reported separately (`Exact`). -/
  | prohibited
  deriving DecidableEq, Repr, Inhabited

/-- The rational `n / d` rounded to an integer according to `mode`.

Intended for `d > 0`; callers normalise the sign of the divisor first (`divRoundZ`).
For `d = 0` the result is `0` (Lean's `x / 0 = 0`); COBOL code paths check for a zero
divisor before calling this (division by zero is a size error). -/
def divRound (mode : RoundingMode) (n d : Int) : Int :=
  match mode with
  | .towardLesser => n / d
  | .towardGreater => -((-n) / d)
  | .truncation => if 0 ≤ n then n / d else -((-n) / d)
  | .prohibited => if 0 ≤ n then n / d else -((-n) / d)
  | .awayFromZero => if 0 ≤ n then -((-n) / d) else n / d
  | .nearestAwayFromZero =>
      if 0 ≤ n then (2 * n + d) / (2 * d) else -((2 * -n + d) / (2 * d))
  | .nearestTowardZero =>
      if 0 ≤ n then (2 * n + d - 1) / (2 * d) else -((2 * -n + d - 1) / (2 * d))
  | .nearestEven =>
      if 2 * (n % d) < d then n / d
      else if d < 2 * (n % d) then n / d + 1
      else if (n / d) % 2 = 0 then n / d else n / d + 1

/-- `divRound` for a divisor of either sign: `n / d = (-n) / (-d)`. -/
def divRoundZ (mode : RoundingMode) (n d : Int) : Int :=
  if d < 0 then divRound mode (-n) (-d) else divRound mode n d

/-- `n / d` is exact (no digits are dropped).  Used for `ROUNDED MODE PROHIBITED`. -/
def Exact (n d : Int) : Prop := n % d = 0

instance (n d : Int) : Decidable (Exact n d) := inferInstanceAs (Decidable (n % d = 0))

/-- Change the scale of the scaled integer `v` from `s` to `t`.  Increasing the scale is
exact; decreasing it divides by a power of ten and rounds by `mode`. -/
def rescale (mode : RoundingMode) (v : Int) (s t : Int) : Int :=
  if s ≤ t then v * 10 ^ (t - s).toNat else divRound mode v (10 ^ (s - t).toNat)

/-- High-order truncation to `n` decimal digits, keeping the sign: what COBOL does when a
result does not fit the receiving item and no `ON SIZE ERROR` phrase is given. -/
def truncDigits (v : Int) (n : Nat) : Int :=
  if 0 ≤ v then v % 10 ^ n else -((-v) % 10 ^ n)

/-- `v` fits in `n` decimal digits. -/
def FitsDigits (v : Int) (n : Nat) : Prop := -(10 ^ n : Int) < v ∧ v < 10 ^ n

instance (v : Int) (n : Nat) : Decidable (FitsDigits v n) := by
  unfold FitsDigits; exact inferInstance

/-! ## Monotonicity

Every rounding mode is monotone in the dividend (for a positive divisor): interval bounds
of a rounded quotient are the rounded quotients of the bounds (`Cobol.Logic.Bounds`). -/

private theorem ediv_nonpos_of_nonpos {a d : Int} (ha : a ≤ 0) (hd : 0 < d) : a / d ≤ 0 := by
  have := Int.ediv_le_ediv hd ha; simpa using this

private theorem ediv_nonneg_of_nonneg {a d : Int} (ha : 0 ≤ a) (hd : 0 < d) : 0 ≤ a / d :=
  Int.ediv_nonneg ha (Int.le_of_lt hd)

private theorem neg_ediv_mono {a b d : Int} (hd : 0 < d) (h : a ≤ b) : -((-a) / d) ≤ -((-b) / d) := by
  have := Int.ediv_le_ediv hd (show -b ≤ -a by omega)
  omega

theorem divRound_mono (m : RoundingMode) {n1 n2 d : Int} (hd : 0 < d) (h : n1 ≤ n2) :
    divRound m n1 d ≤ divRound m n2 d := by
  have hd2 : 0 < 2 * d := by omega
  cases m <;> simp only [divRound]
  · -- awayFromZero
    split <;> split
    · exact neg_ediv_mono hd h
    · omega
    · have := ediv_nonpos_of_nonpos (show n1 ≤ 0 by omega) hd
      have := ediv_nonpos_of_nonpos (show -n2 ≤ 0 by omega) hd
      omega
    · exact Int.ediv_le_ediv hd h
  · -- nearestAwayFromZero
    split <;> split
    · exact Int.ediv_le_ediv hd2 (by omega)
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * -n1 + d by omega) hd2
      have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * n2 + d by omega) hd2
      omega
    · have := Int.ediv_le_ediv hd2 (show 2 * -n2 + d ≤ 2 * -n1 + d by omega)
      omega
  · -- nearestEven
    have hq := Int.ediv_le_ediv hd h
    have e1 := Int.mul_ediv_add_emod n1 d
    have e2 := Int.mul_ediv_add_emod n2 d
    have r1 := Int.emod_nonneg n1 (b := d) (by omega)
    have r2 := Int.emod_nonneg n2 (b := d) (by omega)
    have r1' := Int.emod_lt_of_pos n1 hd
    have r2' := Int.emod_lt_of_pos n2 hd
    by_cases hlt : n1 / d < n2 / d
    · (repeat' split) <;> omega
    · have heq : n1 / d = n2 / d := by omega
      have hr : n1 % d ≤ n2 % d := by
        have : d * (n1 / d) = d * (n2 / d) := by rw [heq]
        omega
      (repeat' split) <;> omega
  · -- nearestTowardZero
    split <;> split
    · exact Int.ediv_le_ediv hd2 (by omega)
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * -n1 + d - 1 by omega) hd2
      have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * n2 + d - 1 by omega) hd2
      omega
    · have := Int.ediv_le_ediv hd2 (show 2 * -n2 + d - 1 ≤ 2 * -n1 + d - 1 by omega)
      omega
  · -- towardGreater
    exact neg_ediv_mono hd h
  · -- towardLesser
    exact Int.ediv_le_ediv hd h
  · -- truncation
    split <;> split
    · exact Int.ediv_le_ediv hd h
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ -n1 by omega) hd
      have := ediv_nonneg_of_nonneg (show 0 ≤ n2 by omega) hd
      omega
    · exact neg_ediv_mono hd h
  · -- prohibited
    split <;> split
    · exact Int.ediv_le_ediv hd h
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ -n1 by omega) hd
      have := ediv_nonneg_of_nonneg (show 0 ≤ n2 by omega) hd
      omega
    · exact neg_ediv_mono hd h

/-! ## Basic facts -/

@[simp] theorem divRound_truncation_nonneg {n d : Int} (h : 0 ≤ n) :
    divRound .truncation n d = n / d := by simp [divRound, h]

@[simp] theorem rescale_same (mode : RoundingMode) (v s : Int) : rescale mode v s s = v := by
  simp [rescale]

theorem rescale_up (mode : RoundingMode) (v : Int) {s t : Int} (h : s ≤ t) :
    rescale mode v s t = v * 10 ^ (t - s).toNat := by simp [rescale, h]

theorem rescale_down (mode : RoundingMode) (v : Int) {s t : Int} (h : t < s) :
    rescale mode v s t = divRound mode v (10 ^ (s - t).toNat) := by
  simp [rescale, Int.not_le.mpr h]

theorem truncDigits_of_fits {v : Int} {n : Nat} (h : FitsDigits v n) : truncDigits v n = v := by
  unfold truncDigits FitsDigits at *
  have hp : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)
  split
  · exact Int.emod_eq_of_lt (by assumption) h.2
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem fitsDigits_truncDigits (v : Int) (n : Nat) : FitsDigits (truncDigits v n) n := by
  unfold truncDigits FitsDigits
  have hp : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)
  have h1 := Int.emod_nonneg v (Int.ne_of_gt hp)
  have h2 := Int.emod_lt_of_pos v hp
  have h3 := Int.emod_nonneg (-v) (Int.ne_of_gt hp)
  have h4 := Int.emod_lt_of_pos (-v) hp
  split <;> omega

/-- Truncating division never increases the magnitude. -/
theorem divRound_truncation_abs_le {n d : Int} (hd : 0 < d) :
    (divRound .truncation n d).natAbs ≤ n.natAbs := by
  simp only [divRound]
  by_cases hn : 0 ≤ n
  · simp only [hn, ↓reduceIte]
    have h1 := Int.ediv_nonneg hn (Int.le_of_lt hd)
    have h2 := Int.ediv_le_self d hn
    omega
  · simp only [hn, ↓reduceIte]
    have h1 := Int.ediv_nonneg (a := -n) (by omega) (Int.le_of_lt hd)
    have h2 := Int.ediv_le_self d (a := -n) (by omega)
    omega

end Cobol
