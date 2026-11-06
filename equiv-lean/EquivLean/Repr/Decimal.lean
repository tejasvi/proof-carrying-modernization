/-!
# Scaled decimals: the shared model of fixed-point values

A COBOL `PICTURE` item, a Java `BigDecimal` and a Rust scaled integer (`i64` cents, `i128`
intermediates) all denote a rational number `unscaled · 10^(-scale)`.  `Decimal` is that
representation, with the arithmetic the three languages share:

* exact `add` / `sub` / `neg` / `mul` (result scales as in `BigDecimal`: `max` for `add` and
  `sub`, the sum for `mul`);
* `rescale x t m`: change the scale to `t`; increasing the scale is exact, decreasing it
  rounds with the mode `m` (COBOL `ROUNDED MODE`, `BigDecimal.setScale`,
  `rust_decimal::round_dp_with_strategy`);
* `div x y t m`: the exact quotient rounded to scale `t` (`BigDecimal.divide(y, t, m)`,
  COBOL `DIVIDE ... ROUNDED`), `none` for a zero divisor;
* `cmp`: numeric comparison, independent of the scales (`BigDecimal.compareTo`).

`Decimal.val` is the value in `Rat` (core Lean), so specifications can be stated with
rational arithmetic; `Decimal.roundRat m q` rounds a rational to an integer, and every rounding
operation is specified by it (`divRound_eq_roundRat`, `divRoundZ_eq_roundRat`, `val_rescale`,
`quotInt_eq_roundRat`, `div_eq_roundRat`).  The single rounding primitive is `Decimal.divRound m n d`, the integer
`n / d` (`d > 0`) rounded by `m`, written with `Int` Euclidean division and `if` only, so
goals with literal divisors are decided by `omega`.  Its arms are literally those of
`Cobol.divRound` (coblean), which makes the COBOL bridge definitional.

Every bridge maps its encoding's values here: `EquivLean.Cobol` (PIC fields, coblean's
`Java.BigDecimal` and Rust models), the Jimple bridge (`Jimple.BigDec`), the Aeneas bridge
(scaled `Std.I64` / `Std.I128`).

Core Lean only: this file must not import an encoding.
-/

namespace EquivLean

/-- Rounding modes, under their `java.math.RoundingMode` names (`UNNECESSARY` is not a
rounding: it is "exact or throw", expressed with `Decimal.ExactAt`).  COBOL 2014
`ROUNDED MODE` and `rust_decimal::RoundingStrategy` names in the comments. -/
inductive RoundingMode where
  /-- Away from zero.  COBOL `AWAY-FROM-ZERO`, Rust `AwayFromZero`. -/
  | UP
  /-- Toward zero.  COBOL `TRUNCATION` (no `ROUNDED` phrase), Rust `ToZero`. -/
  | DOWN
  /-- Toward +∞.  COBOL `TOWARD-GREATER`, Rust `ToPositiveInfinity`. -/
  | CEILING
  /-- Toward −∞.  COBOL `TOWARD-LESSER`, Rust `ToNegativeInfinity`. -/
  | FLOOR
  /-- Nearest, ties away from zero.  COBOL `NEAREST-AWAY-FROM-ZERO` (plain `ROUNDED`),
  Rust `MidpointAwayFromZero`. -/
  | HALF_UP
  /-- Nearest, ties toward zero.  COBOL `NEAREST-TOWARD-ZERO`, Rust `MidpointTowardZero`. -/
  | HALF_DOWN
  /-- Nearest, ties to even.  COBOL `NEAREST-EVEN`, Rust `MidpointNearestEven`. -/
  | HALF_EVEN
  deriving DecidableEq, Repr, Inhabited

/-- A scaled decimal: the value `unscaled · 10^(-scale)`.  The scale is an `Int` (COBOL
`PIC 99PPP` and `BigDecimal` allow negative scales). -/
structure Decimal where
  unscaled : Int
  scale : Int
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

/-! ## Integer rounding -/

/-- The integer `n / d` rounded by `m`, for a divisor `d > 0` (for `d = 0` the result is `0`,
Lean's `n / 0`; callers test for a zero divisor first). -/
def divRound (m : RoundingMode) (n d : Int) : Int :=
  match m with
  | .FLOOR => n / d
  | .CEILING => -((-n) / d)
  | .DOWN => if 0 ≤ n then n / d else -((-n) / d)
  | .UP => if 0 ≤ n then -((-n) / d) else n / d
  | .HALF_UP => if 0 ≤ n then (2 * n + d) / (2 * d) else -((2 * -n + d) / (2 * d))
  | .HALF_DOWN =>
      if 0 ≤ n then (2 * n + d - 1) / (2 * d) else -((2 * -n + d - 1) / (2 * d))
  | .HALF_EVEN =>
      if 2 * (n % d) < d then n / d
      else if d < 2 * (n % d) then n / d + 1
      else if (n / d) % 2 = 0 then n / d else n / d + 1

/-- `divRound` for a nonzero divisor of either sign (`n / d = (-n) / (-d)`). -/
def divRoundZ (m : RoundingMode) (n d : Int) : Int :=
  if d < 0 then divRound m (-n) (-d) else divRound m n d

/-! ## Decimals -/

/-- The value of a decimal, as a rational number. -/
def val (x : Decimal) : Rat := (x.unscaled : Rat) * (10 : Rat) ^ (-x.scale)

/-- The unscaled value at a scale `t ≥ x.scale` (exact: multiply by `10^(t - scale)`). -/
def align (x : Decimal) (t : Int) : Int := x.unscaled * 10 ^ (t - x.scale).toNat

/-- The common scale of two decimals (the larger one). -/
def common (x y : Decimal) : Int := max x.scale y.scale

def zero : Decimal := ⟨0, 0⟩

def neg (x : Decimal) : Decimal := ⟨-x.unscaled, x.scale⟩

/-- Exact sum, at the larger scale. -/
def add (x y : Decimal) : Decimal := ⟨x.align (common x y) + y.align (common x y), common x y⟩

/-- Exact difference, at the larger scale. -/
def sub (x y : Decimal) : Decimal := ⟨x.align (common x y) - y.align (common x y), common x y⟩

/-- Exact product, at the sum of the scales. -/
def mul (x y : Decimal) : Decimal := ⟨x.unscaled * y.unscaled, x.scale + y.scale⟩

instance : Neg Decimal := ⟨neg⟩
instance : Add Decimal := ⟨add⟩
instance : Sub Decimal := ⟨sub⟩
instance : Mul Decimal := ⟨mul⟩

/-- The unscaled value of `x` rescaled to `t` with mode `m`. -/
def rescaleInt (x : Decimal) (t : Int) (m : RoundingMode) : Int :=
  if x.scale ≤ t then x.align t else divRound m x.unscaled (10 ^ (x.scale - t).toNat)

/-- Rescale to `t`: exact if `t ≥ scale`, otherwise rounded by `m`. -/
def rescale (x : Decimal) (t : Int) (m : RoundingMode) : Decimal := ⟨x.rescaleInt t m, t⟩

/-- `x` is representable at scale `t` without loss (the condition under which
`BigDecimal.setScale(t, UNNECESSARY)` and COBOL `ROUNDED MODE PROHIBITED` succeed). -/
def ExactAt (x : Decimal) (t : Int) : Prop :=
  t < x.scale → x.unscaled % 10 ^ (x.scale - t).toNat = 0

instance (x : Decimal) (t : Int) : Decidable (x.ExactAt t) := by
  unfold ExactAt; exact inferInstance

/-- The unscaled quotient `x / y` at scale `t`, rounded by `m` (`y.unscaled ≠ 0`). -/
def quotInt (x y : Decimal) (t : Int) (m : RoundingMode) : Int :=
  if 0 ≤ t - x.scale + y.scale then
    divRoundZ m (x.unscaled * 10 ^ (t - x.scale + y.scale).toNat) y.unscaled
  else divRoundZ m x.unscaled (y.unscaled * 10 ^ (-(t - x.scale + y.scale)).toNat)

/-- The quotient `x / y` rounded to scale `t` by `m`; `none` when `y` is zero. -/
def div (x y : Decimal) (t : Int) (m : RoundingMode) : Option Decimal :=
  if y.unscaled = 0 then none else some ⟨x.quotInt y t m, t⟩

/-- Numeric comparison (scale-insensitive: `2.0` and `2.00` compare equal). -/
def cmp (x y : Decimal) : Ordering := compare (x.align (common x y)) (y.align (common x y))

/-! ## Powers of ten in `Rat` -/

theorem ten_ne_zero : (10 : Rat) ≠ 0 := by decide

theorem zpow10_pos (k : Int) : (0 : Rat) < (10 : Rat) ^ k := Rat.zpow_pos (by decide)

theorem zpow10_mul_neg (k : Int) : (10 : Rat) ^ k * (10 : Rat) ^ (-k) = 1 := by
  rw [← Rat.zpow_add ten_ne_zero, show k + -k = 0 by omega, Rat.zpow_zero]

theorem zpow10_add (a b : Int) : (10 : Rat) ^ (a + b) = (10 : Rat) ^ a * (10 : Rat) ^ b :=
  Rat.zpow_add ten_ne_zero a b

theorem intCast_pow10 (k : Nat) : (((10 : Int) ^ k : Int) : Rat) = (10 : Rat) ^ (k : Int) := by
  rw [Rat.intCast_pow, Rat.zpow_natCast]; rfl

theorem pow10_pos (k : Nat) : (0 : Int) < 10 ^ k := Int.pow_pos (by decide)

/-! ## Values -/

@[simp] theorem val_mk (u s : Int) : (Decimal.mk u s).val = (u : Rat) * (10 : Rat) ^ (-s) := rfl

/-- Aligning to a larger scale keeps the value. -/
theorem val_align (x : Decimal) {t : Int} (h : x.scale ≤ t) :
    (Decimal.mk (x.align t) t).val = x.val := by
  simp only [val, align]
  rw [Rat.intCast_mul, intCast_pow10, Int.toNat_of_nonneg (by omega), Rat.mul_assoc,
    ← zpow10_add, show t - x.scale + -t = -x.scale by omega]

theorem common_le_left (x y : Decimal) : x.scale ≤ common x y := Int.le_max_left _ _
theorem common_le_right (x y : Decimal) : y.scale ≤ common x y := Int.le_max_right _ _

@[simp] theorem val_zero : zero.val = 0 := by simp [zero, val]

@[simp] theorem val_neg (x : Decimal) : x.neg.val = -x.val := by
  simp only [neg, val, Rat.intCast_neg, Rat.neg_mul]

@[simp] theorem val_add (x y : Decimal) : (x.add y).val = x.val + y.val := by
  have hx := val_align x (common_le_left x y)
  have hy := val_align y (common_le_right x y)
  simp only [val] at hx hy ⊢
  simp only [add, Rat.intCast_add, Rat.add_mul, hx, hy]

@[simp] theorem val_sub (x y : Decimal) : (x.sub y).val = x.val - y.val := by
  have hx := val_align x (common_le_left x y)
  have hy := val_align y (common_le_right x y)
  simp only [val] at hx hy ⊢
  simp only [sub, Rat.intCast_sub, Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, hx, hy]

@[simp] theorem val_mul (x y : Decimal) : (x.mul y).val = x.val * y.val := by
  simp only [mul, val, Rat.intCast_mul, Int.neg_add, zpow10_add]
  grind

/-- Decimals at the same scale have the same value exactly when they are equal. -/
theorem val_inj_of_scale {x y : Decimal} (h : x.scale = y.scale) : x.val = y.val ↔ x = y := by
  constructor
  · intro hv
    obtain ⟨xu, xs⟩ := x
    obtain ⟨yu, ys⟩ := y
    simp only at h
    subst h
    have hp := zpow10_pos (-xs)
    simp only [val] at hv
    have : (xu : Rat) = yu := by
      have h1 := congrArg (· * (10 : Rat) ^ xs) hv
      simp only [Rat.mul_assoc] at h1
      rwa [show (10 : Rat) ^ (-xs) * 10 ^ xs = 1 by
        rw [← zpow10_add, show -xs + xs = 0 by omega, Rat.zpow_zero], Rat.mul_one,
        Rat.mul_one] at h1
    rw [Rat.intCast_inj.1 this]
  · rintro rfl; rfl

theorem val_le_of_scale {x y : Decimal} (h : x.scale = y.scale) :
    x.val ≤ y.val ↔ x.unscaled ≤ y.unscaled := by
  simp only [val, h]
  constructor
  · intro hv
    exact Rat.intCast_le_intCast.1 (Rat.le_of_mul_le_mul_right hv (zpow10_pos _))
  · intro hu
    exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.2 hu)
      (Rat.le_of_lt (zpow10_pos _))

theorem val_lt_of_scale {x y : Decimal} (h : x.scale = y.scale) :
    x.val < y.val ↔ x.unscaled < y.unscaled := by
  simp only [val, h]
  rw [Rat.mul_lt_mul_right (zpow10_pos _)]
  exact Rat.intCast_lt_intCast

/-! ## Comparison -/

theorem cmp_eq_lt_iff (x y : Decimal) : x.cmp y = .lt ↔ x.val < y.val := by
  rw [← val_align x (common_le_left x y), ← val_align y (common_le_right x y),
    val_lt_of_scale (x := ⟨x.align (common x y), common x y⟩)
      (y := ⟨y.align (common x y), common x y⟩) rfl]
  simp only [cmp]
  exact Int.compare_eq_lt

theorem cmp_eq_gt_iff (x y : Decimal) : x.cmp y = .gt ↔ y.val < x.val := by
  rw [← val_align x (common_le_left x y), ← val_align y (common_le_right x y),
    val_lt_of_scale (x := ⟨y.align (common x y), common x y⟩)
      (y := ⟨x.align (common x y), common x y⟩) rfl]
  simp only [cmp]
  exact Int.compare_eq_gt

theorem cmp_eq_eq_iff (x y : Decimal) : x.cmp y = .eq ↔ x.val = y.val := by
  rw [← val_align x (common_le_left x y), ← val_align y (common_le_right x y),
    val_inj_of_scale (x := ⟨x.align (common x y), common x y⟩)
      (y := ⟨y.align (common x y), common x y⟩) rfl]
  simp only [cmp, Decimal.mk.injEq, and_true]
  exact Int.compare_eq_eq

/-! ## Rounding: exact results, monotonicity, error bound -/

/-- Rounding an exact quotient returns it, in every mode. -/
theorem divRound_mul_self (m : RoundingMode) (q : Int) {d : Int} (hd : 0 < d) :
    divRound m (q * d) d = q := by
  have hd0 : d ≠ 0 := by omega
  have h1 : q * d / d = q := Int.mul_ediv_cancel q hd0
  have h2 : -(q * d) / d = -q := by
    rw [← Int.neg_mul, Int.mul_ediv_cancel _ hd0]
  have h3 : (2 * (q * d) + d) / (2 * d) = q := by
    rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
  have h4 : (2 * -(q * d) + d) / (2 * d) = -q := by
    rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
  have h5 : (2 * (q * d) + d - 1) / (2 * d) = q := by
    rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
  have h6 : (2 * -(q * d) + d - 1) / (2 * d) = -q := by
    rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
  have h7 : q * d % d = 0 := Int.mul_emod_left q d
  cases m <;> simp only [divRound] <;> (try split) <;> (try split) <;> (try split) <;> omega

private theorem ediv_nonpos_of_nonpos {a d : Int} (ha : a ≤ 0) (hd : 0 < d) : a / d ≤ 0 := by
  have := Int.ediv_le_ediv hd ha; simpa using this

private theorem ediv_nonneg_of_nonneg {a d : Int} (ha : 0 ≤ a) (hd : 0 < d) : 0 ≤ a / d :=
  Int.ediv_nonneg ha (Int.le_of_lt hd)

private theorem neg_ediv_mono {a b d : Int} (hd : 0 < d) (h : a ≤ b) :
    -((-a) / d) ≤ -((-b) / d) := by
  have := Int.ediv_le_ediv hd (show -b ≤ -a by omega)
  omega

/-- Every rounding mode is monotone in the dividend. -/
theorem divRound_mono (m : RoundingMode) {n1 n2 d : Int} (hd : 0 < d) (h : n1 ≤ n2) :
    divRound m n1 d ≤ divRound m n2 d := by
  have hd2 : 0 < 2 * d := by omega
  cases m <;> simp only [divRound]
  · -- UP
    split <;> split
    · exact neg_ediv_mono hd h
    · omega
    · have := ediv_nonpos_of_nonpos (show n1 ≤ 0 by omega) hd
      have := ediv_nonpos_of_nonpos (show -n2 ≤ 0 by omega) hd
      omega
    · exact Int.ediv_le_ediv hd h
  · -- DOWN
    split <;> split
    · exact Int.ediv_le_ediv hd h
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ -n1 by omega) hd
      have := ediv_nonneg_of_nonneg (show 0 ≤ n2 by omega) hd
      omega
    · exact neg_ediv_mono hd h
  · -- CEILING
    exact neg_ediv_mono hd h
  · -- FLOOR
    exact Int.ediv_le_ediv hd h
  · -- HALF_UP
    split <;> split
    · exact Int.ediv_le_ediv hd2 (by omega)
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * -n1 + d by omega) hd2
      have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * n2 + d by omega) hd2
      omega
    · have := Int.ediv_le_ediv hd2 (show 2 * -n2 + d ≤ 2 * -n1 + d by omega)
      omega
  · -- HALF_DOWN
    split <;> split
    · exact Int.ediv_le_ediv hd2 (by omega)
    · omega
    · have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * -n1 + d - 1 by omega) hd2
      have := ediv_nonneg_of_nonneg (show 0 ≤ 2 * n2 + d - 1 by omega) hd2
      omega
    · have := Int.ediv_le_ediv hd2 (show 2 * -n2 + d - 1 ≤ 2 * -n1 + d - 1 by omega)
      omega
  · -- HALF_EVEN
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

/-- The rounded quotient is the floor or the floor plus one, in every mode: rounding errs by
less than one unit. -/
theorem divRound_floor_or_succ (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    divRound m n d = n / d ∨ divRound m n d = n / d + 1 := by
  have e := Int.mul_ediv_add_emod n d
  have r0 := Int.emod_nonneg n (b := d) (by omega)
  have r1 := Int.emod_lt_of_pos n hd
  -- the ceiling `-((-n) / d)` is the floor or the floor plus one
  have hc : -((-n) / d) = n / d ∨ -((-n) / d) = n / d + 1 := by
    by_cases hr : n % d = 0
    · left
      have : -n = (-(n / d)) * d := by rw [Int.neg_mul, Int.mul_comm]; omega
      rw [this, Int.mul_ediv_cancel _ (by omega)]; omega
    · right
      have : (-n) / d = -(n / d) - 1 := by
        rw [Int.ediv_eq_iff_of_pos hd]; constructor <;> grind
      omega
  -- the nearest modes: `(2n + d - c) / (2d)` for `c ∈ {0, 1}`, and their mirror images
  have hn : ∀ c : Int, 0 ≤ c → c ≤ 1 →
      (2 * n + d - c) / (2 * d) = n / d ∨ (2 * n + d - c) / (2 * d) = n / d + 1 := by
    intro c hc0 hc1
    by_cases h2 : 2 * (n % d) + d - c < 2 * d
    · left; rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
    · right; rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
  have hn' : ∀ c : Int, 0 ≤ c → c ≤ 1 →
      -((2 * -n + d - c) / (2 * d)) = n / d ∨ -((2 * -n + d - c) / (2 * d)) = n / d + 1 := by
    intro c hc0 hc1
    -- `-n = d * (-(n / d) - 1) + (d - n % d)` when the remainder is nonzero
    by_cases hr : n % d = 0
    · have : (2 * -n + d - c) / (2 * d) = -(n / d) := by
        rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
      omega
    · by_cases h2 : 2 * (d - n % d) + d - c < 2 * d
      · have : (2 * -n + d - c) / (2 * d) = -(n / d) - 1 := by
          rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
        omega
      · have : (2 * -n + d - c) / (2 * d) = -(n / d) := by
          rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind
        omega
  have hu := hn 0 (by omega) (by omega)
  have hl := hn 1 (by omega) (by omega)
  have hu' := hn' 0 (by omega) (by omega)
  have hl' := hn' 1 (by omega) (by omega)
  simp only [Int.sub_zero] at hu hu'
  cases m
  · simp only [divRound]; split <;> omega
  · simp only [divRound]; split <;> omega
  · exact hc
  · exact Or.inl rfl
  · simp only [divRound]; split <;> omega
  · simp only [divRound]; split <;> omega
  · simp only [divRound]; (repeat' split) <;> omega

/-! ## Rescaling -/

@[simp] theorem rescale_scale (x : Decimal) (t : Int) (m : RoundingMode) :
    (x.rescale t m).scale = t := rfl

@[simp] theorem rescale_unscaled (x : Decimal) (t : Int) (m : RoundingMode) :
    (x.rescale t m).unscaled = x.rescaleInt t m := rfl

theorem rescaleInt_of_le (x : Decimal) {t : Int} (m : RoundingMode) (h : x.scale ≤ t) :
    x.rescaleInt t m = x.align t := by simp [rescaleInt, h]

theorem rescaleInt_of_lt (x : Decimal) {t : Int} (m : RoundingMode) (h : t < x.scale) :
    x.rescaleInt t m = divRound m x.unscaled (10 ^ (x.scale - t).toNat) := by
  simp [rescaleInt, Int.not_le.2 h]

/-- Rescaling to the same scale is the identity. -/
@[simp] theorem rescale_self (x : Decimal) (m : RoundingMode) : x.rescale x.scale m = x := by
  simp [rescale, rescaleInt, align]

/-- Increasing the scale keeps the value. -/
theorem val_rescale_of_le (x : Decimal) {t : Int} (m : RoundingMode) (h : x.scale ≤ t) :
    (x.rescale t m).val = x.val := by
  simp only [rescale, rescaleInt_of_le x m h]
  exact val_align x h

/-- **Idempotence.**  A decimal already at scale `t` is not changed by rescaling to `t`. -/
@[simp] theorem rescale_rescale_same (x : Decimal) (t : Int) (m m' : RoundingMode) :
    (x.rescale t m).rescale t m' = x.rescale t m := rescale_self _ _

/-- **Exact results.**  If `x` is representable at scale `t`, rounding to `t` returns the exact
value in every mode. -/
theorem rescale_of_exact (x : Decimal) {t : Int} (m : RoundingMode) (h : x.ExactAt t) :
    (x.rescale t m).val = x.val := by
  by_cases ht : x.scale ≤ t
  · exact val_rescale_of_le x m ht
  · have ht' : t < x.scale := by omega
    have hd := pow10_pos (x.scale - t).toNat
    have hdvd := h ht'
    have hq : x.unscaled = (x.unscaled / 10 ^ (x.scale - t).toNat) * 10 ^ (x.scale - t).toNat := by
      have := Int.mul_ediv_add_emod x.unscaled (10 ^ (x.scale - t).toNat)
      rw [Int.mul_comm]; omega
    have hr : x.rescaleInt t m = x.unscaled / 10 ^ (x.scale - t).toNat := by
      rw [rescaleInt_of_lt x m ht']
      conv => lhs; rw [hq]
      exact divRound_mul_self m _ hd
    simp only [rescale, hr, val]
    conv => rhs; rw [hq]
    rw [Rat.intCast_mul, intCast_pow10, Int.toNat_of_nonneg (by omega), Rat.mul_assoc,
      ← zpow10_add, show x.scale - t + -x.scale = -t by omega]

/-- The same, at the level of unscaled values. -/
theorem rescaleInt_of_exact {q : Int} {s t : Int} (m : RoundingMode) (h : t ≤ s) :
    (Decimal.mk (q * 10 ^ (s - t).toNat) s).rescaleInt t m = q := by
  by_cases hst : s ≤ t
  · have : s = t := by omega
    subst this
    simp [rescaleInt, align]
  · rw [rescaleInt_of_lt _ m (by simp only; omega)]
    exact divRound_mul_self m q (pow10_pos _)

/-- **Monotonicity.**  Rescaling preserves the order of decimals at a common scale. -/
theorem rescale_mono {x y : Decimal} (hs : x.scale = y.scale) (h : x.val ≤ y.val) (t : Int)
    (m : RoundingMode) : (x.rescale t m).val ≤ (y.rescale t m).val := by
  rw [val_le_of_scale (by simp)]
  rw [val_le_of_scale hs] at h
  simp only [rescale_unscaled, rescaleInt, align, hs]
  split
  · exact Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (pow10_pos _))
  · exact divRound_mono m (pow10_pos _) h

/-- Rounding to scale `t` errs by less than one unit of `10^(-t)`. -/
theorem rescaleInt_floor_or_succ (x : Decimal) {t : Int} (m : RoundingMode) (h : t < x.scale) :
    x.rescaleInt t m = x.rescaleInt t .FLOOR ∨ x.rescaleInt t m = x.rescaleInt t .FLOOR + 1 := by
  rw [rescaleInt_of_lt x m h, rescaleInt_of_lt x .FLOOR h]
  exact divRound_floor_or_succ m _ (pow10_pos _)

/-! ## Division -/

theorem div_eq_none_iff (x y : Decimal) (t : Int) (m : RoundingMode) :
    x.div y t m = none ↔ y.unscaled = 0 := by
  unfold div; split <;> simp_all

theorem div_of_ne_zero (x y : Decimal) (t : Int) (m : RoundingMode) (h : y.unscaled ≠ 0) :
    x.div y t m = some ⟨x.quotInt y t m, t⟩ := by
  simp [div, h]

/-! ## Rounding in `Rat`: the specification

`divRound m n d` is the rational quotient `n / d` rounded by `m` (`divRound_eq_roundRat`), and
the unscaled value of a rescale is `x · 10^t` rounded (`rescaleInt_eq_roundRat`, `val_rescale`). -/

/-- Rounding a rational number to an integer as `java.math.RoundingMode` specifies: the floor,
the ceiling, toward / away from zero, or the nearest integer with the mode's tie rule.  The arms
are those of JimpleLean's `roundRat` (without `UNNECESSARY`), so the two specifications agree
by `rfl` per mode. -/
def roundRat (m : RoundingMode) (q : Rat) : Int :=
  match m with
  | .UP => if 0 ≤ q then q.ceil else q.floor
  | .DOWN => if 0 ≤ q then q.floor else q.ceil
  | .CEILING => q.ceil
  | .FLOOR => q.floor
  | .HALF_UP =>
      if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else if 0 ≤ q then q.ceil else q.floor
  | .HALF_DOWN =>
      if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else if 0 ≤ q then q.floor else q.ceil
  | .HALF_EVEN =>
      if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else if q.floor % 2 = 0 then q.floor else q.ceil

theorem floor_intCast_div (n : Int) {d : Int} (hd : 0 < d) : ((n : Rat) / d).floor = n / d := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.2 hd
  apply Int.le_antisymm
  · have : ((n : Rat) / d).floor < n / d + 1 := by
      rw [Rat.floor_lt_iff, Rat.div_lt_iff hdR]
      have := Int.lt_ediv_add_one_mul_self n hd
      exact_mod_cast this
    omega
  · rw [Rat.le_floor_iff, ← Rat.not_lt, Rat.div_lt_iff hdR]
    have := Int.ediv_mul_le n (Int.ne_of_gt hd)
    intro h
    have h' : n < n / d * d := by exact_mod_cast h
    omega

theorem ceil_intCast_div (n : Int) {d : Int} (hd : 0 < d) : ((n : Rat) / d).ceil = -((-n) / d) := by
  rw [Rat.ceil_eq_neg_floor_neg, show -((n : Rat) / d) = ((-n : Int) : Rat) / d by push_cast; grind,
    floor_intCast_div _ hd]

/-- `q - a < 1/2` for `q = n / d`, in integers. -/
theorem sub_lt_half_iff (n a : Int) {d : Int} (hd : 0 < d) :
    (n : Rat) / d - (a : Rat) < 1/2 ↔ 2 * (n - a * d) < d := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.2 hd
  rw [Rat.sub_lt_iff, Rat.div_lt_iff hdR]
  constructor
  · intro h
    have : ((2 * n : Int) : Rat) < (((2 * a + 1) * d : Int) : Rat) := by push_cast; grind
    have := Rat.intCast_lt_intCast.1 this
    grind
  · intro h
    have : 2 * n < (2 * a + 1) * d := by grind
    have h2 : ((2 * n : Int) : Rat) < (((2 * a + 1) * d : Int) : Rat) := by exact_mod_cast this
    push_cast at h2
    grind

/-- `a - q < 1/2` for `q = n / d`, in integers. -/
theorem sub_lt_half_iff' (n a : Int) {d : Int} (hd : 0 < d) :
    (a : Rat) - (n : Rat) / d < 1/2 ↔ 2 * (a * d - n) < d := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.2 hd
  constructor
  · intro h
    have h1 : (a : Rat) - 1/2 < (n : Rat) / d := by grind
    rw [Rat.lt_div_iff hdR] at h1
    have : (((2 * a - 1) * d : Int) : Rat) < ((2 * n : Int) : Rat) := by push_cast; grind
    have := Rat.intCast_lt_intCast.1 this
    grind
  · intro h
    have : (2 * a - 1) * d < 2 * n := by grind
    have h2 : (((2 * a - 1) * d : Int) : Rat) < ((2 * n : Int) : Rat) := by exact_mod_cast this
    push_cast at h2
    have h1 : ((a : Rat) - 1/2) * d < n := by grind
    rw [← Rat.lt_div_iff hdR] at h1
    grind

theorem nonneg_div_iff (n : Int) {d : Int} (hd : 0 < d) : (0 : Rat) ≤ (n : Rat) / d ↔ 0 ≤ n := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.2 hd
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hn' : ((n : Int) : Rat) < 0 := by exact_mod_cast (show n < 0 by omega)
    have : (n : Rat) / d < 0 := by rw [Rat.div_lt_iff hdR, Rat.zero_mul]; exact hn'
    exact absurd h (Rat.not_le.2 this)
  · intro h
    rw [← Rat.not_lt, Rat.div_lt_iff hdR, Rat.zero_mul]
    intro h'; have : n < 0 := by exact_mod_cast h'
    omega

theorem neg_ediv_cases (n : Int) {d : Int} (hd : 0 < d) :
    (-n) / d = (if n % d = 0 then -(n / d) else -(n / d) - 1) := by
  have e := Int.mul_ediv_add_emod n d
  have r0 := Int.emod_nonneg n (b := d) (by omega)
  have r1 := Int.emod_lt_of_pos n hd
  split <;> (rw [Int.ediv_eq_iff_of_pos hd]; constructor <;> grind)

theorem half_div (x c : Int) {d : Int} (hd : 0 < d) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (2 * x + d - c) / (2 * d) = if 2 * (x % d) + d - c < 2 * d then x / d else x / d + 1 := by
  have e := Int.mul_ediv_add_emod x d
  have r0 := Int.emod_nonneg x (b := d) (by omega)
  have r1 := Int.emod_lt_of_pos x hd
  split <;> (rw [Int.ediv_eq_iff_of_pos (by omega)]; constructor <;> grind)

theorem divRound_eq_roundRat (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    divRound m n d = roundRat m ((n : Rat) / d) := by
  have e : n / d * d + n % d = n := by rw [Int.mul_comm]; exact Int.mul_ediv_add_emod n d
  have r0 := Int.emod_nonneg n (b := d) (by omega)
  have r1 := Int.emod_lt_of_pos n hd
  have hneg := neg_ediv_cases n hd
  have hA := sub_lt_half_iff n (n / d) hd
  have hS := nonneg_div_iff n hd
  have hfl := floor_intCast_div n hd
  have hu := half_div n 0 hd (by omega) (by omega)
  have hl := half_div n 1 hd (by omega) (by omega)
  have hu' := half_div (-n) 0 hd (by omega) (by omega)
  have hl' := half_div (-n) 1 hd (by omega) (by omega)
  simp only [Int.sub_zero] at hu hu'
  by_cases hR : n % d = 0
  · have hq : (-n) / d = -(n / d) := by rw [hneg, ite_eq_left hR]
    have hr : (-n) % d = 0 := by rw [Int.emod_def, hq, Int.mul_neg, Int.mul_comm]; omega
    have hce : ((n : Rat) / d).ceil = n / d := by rw [ceil_intCast_div n hd, hq, Int.neg_neg]
    have hB := sub_lt_half_iff' n (n / d) hd
    rw [hr, hq] at hu' hl'
    cases m <;> simp only [divRound, roundRat, hfl, hce, hA, hB, hS, hq, Int.neg_neg] <;>
      (repeat' split) <;> omega
  · have hq : (-n) / d = -(n / d) - 1 := by rw [hneg, ite_eq_right hR]
    have hr : (-n) % d = d - n % d := by
      rw [Int.emod_def, hq, Int.mul_sub, Int.mul_neg, Int.mul_one, Int.mul_comm d]; omega
    have hc : -((-n) / d) = n / d + 1 := by rw [hq]; omega
    have hce : ((n : Rat) / d).ceil = n / d + 1 := by rw [ceil_intCast_div n hd, hc]
    have hB := sub_lt_half_iff' n (n / d + 1) hd
    rw [Int.add_mul, Int.one_mul] at hB
    rw [hr, hq] at hu' hl'
    cases m <;> simp only [divRound, roundRat, hfl, hce, hA, hB, hS, hq] <;>
      (repeat' split) <;> omega

/-- `divRoundZ` (either sign of divisor) rounds the rational quotient. -/
theorem divRoundZ_eq_roundRat (m : RoundingMode) (n : Int) {d : Int} (hd : d ≠ 0) :
    divRoundZ m n d = roundRat m ((n : Rat) / d) := by
  unfold divRoundZ
  split
  · rw [divRound_eq_roundRat m (-n) (by omega)]
    congr 1
    push_cast
    grind
  · exact divRound_eq_roundRat m n (by omega)

/-- Rounding an integer gives it back, in every mode. -/
theorem roundRat_intCast (m : RoundingMode) (k : Int) : roundRat m (k : Rat) = k := by
  have h : (k : Rat) - (k : Rat) < 1/2 := by grind
  cases m <;> simp [roundRat, Rat.floor_intCast, Rat.ceil_intCast, h]

theorem val_mul_zpow_of_lt (x : Decimal) {t : Int} (h : t < x.scale) :
    x.val * (10 : Rat) ^ t = (x.unscaled : Rat) / (((10 : Int) ^ (x.scale - t).toNat : Int) : Rat) := by
  rw [intCast_pow10, Int.toNat_of_nonneg (by omega), Rat.div_def, ← Rat.zpow_neg, val, Rat.mul_assoc,
    ← zpow10_add, show -x.scale + t = -(x.scale - t) by omega]

theorem val_mul_zpow_of_le (x : Decimal) {t : Int} (h : x.scale ≤ t) :
    x.val * (10 : Rat) ^ t = ((x.align t : Int) : Rat) := by
  rw [align, Rat.intCast_mul, intCast_pow10, Int.toNat_of_nonneg (by omega), val, Rat.mul_assoc,
    ← zpow10_add, show -x.scale + t = t - x.scale by omega]

/-- **Value of a rescale**: the unscaled result is the rational `x · 10^t` rounded by `m`. -/
theorem rescaleInt_eq_roundRat (x : Decimal) (t : Int) (m : RoundingMode) :
    x.rescaleInt t m = roundRat m (x.val * (10 : Rat) ^ t) := by
  by_cases h : x.scale ≤ t
  · rw [rescaleInt_of_le x m h, val_mul_zpow_of_le x h, roundRat_intCast]
  · rw [rescaleInt_of_lt x m (by omega), val_mul_zpow_of_lt x (by omega),
      divRound_eq_roundRat m _ (pow10_pos _)]

theorem val_rescale (x : Decimal) (t : Int) (m : RoundingMode) :
    (x.rescale t m).val = (roundRat m (x.val * (10 : Rat) ^ t) : Rat) * (10 : Rat) ^ (-t) := by
  rw [← rescaleInt_eq_roundRat]; rfl

theorem val_div_mul_zpow (x y : Decimal) (t : Int) :
    x.val / y.val * (10 : Rat) ^ t =
      (x.unscaled : Rat) / y.unscaled * (10 : Rat) ^ (t - x.scale + y.scale) := by
  simp only [val]
  have h1 : (10 : Rat) ^ (t - x.scale + y.scale) = (10 : Rat) ^ t * (10 : Rat) ^ (-x.scale) * ((10 : Rat) ^ (-y.scale))⁻¹ := by
    rw [← Rat.zpow_neg, ← zpow10_add, ← zpow10_add]; congr 1; omega
  have h2 : (10 : Rat) ^ (-y.scale) ≠ 0 := Rat.ne_of_gt (zpow10_pos _)
  rw [h1]
  grind

/-- **Value of a quotient**: the unscaled result of `div` is `x / y · 10^t` rounded by `m`. -/
theorem quotInt_eq_roundRat (x y : Decimal) (t : Int) (m : RoundingMode) (hy : y.unscaled ≠ 0) :
    x.quotInt y t m = roundRat m (x.val / y.val * (10 : Rat) ^ t) := by
  have hyR : (y.unscaled : Rat) ≠ 0 := by exact_mod_cast hy
  rw [val_div_mul_zpow]
  unfold quotInt
  split
  · rename_i he
    rw [divRoundZ_eq_roundRat m _ hy]
    congr 1
    rw [Rat.intCast_mul, intCast_pow10, Int.toNat_of_nonneg he]
    grind
  · rename_i he
    have hd : y.unscaled * 10 ^ (-(t - x.scale + y.scale)).toNat ≠ 0 :=
      Int.mul_ne_zero hy (Int.ne_of_gt (pow10_pos _))
    rw [divRoundZ_eq_roundRat m _ hd]
    congr 1
    rw [Rat.intCast_mul, intCast_pow10, Int.toNat_of_nonneg (by omega), Rat.zpow_neg]
    have h3 : (10 : Rat) ^ (t - x.scale + y.scale) ≠ 0 := Rat.ne_of_gt (zpow10_pos _)
    grind

theorem div_eq_roundRat (x y : Decimal) (t : Int) (m : RoundingMode) (hy : y.unscaled ≠ 0) :
    x.div y t m = some ⟨roundRat m (x.val / y.val * (10 : Rat) ^ t), t⟩ := by
  rw [div_of_ne_zero x y t m hy, quotInt_eq_roundRat x y t m hy]

end Decimal

end EquivLean
