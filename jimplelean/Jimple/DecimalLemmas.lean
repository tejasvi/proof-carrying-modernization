/-
  Jimple/DecimalLemmas.lean

  `BigDec` (`Jimple/Decimal.lean`) in `Rat`: what each operation does to the value `toRat`,
  and `java.math.RoundingMode` as a specification over `Rat` (`roundRat`), so that BigDecimal
  code is verified with rational arithmetic (`simp [jsimp]`, `grind`, `omega`, `decide`).

  * powers of ten: `pow10_add`, `pow10_neg`, `pow10_natCast`, `pow10Int_cast`, ...
  * values: `toRat_add`, `toRat_sub`, `toRat_mul`, `toRat_negate`, `toRat_abs`, ...
    (`@[simp, jsimp]`), and comparison through values (`compareTo_eq`,
    `compareTo_lt_zero_iff`, `toRat_max`, ...)
  * rounding: `roundRat` and its error bounds; `divRound_eq` (the integer algorithm rounds the
    exact quotient), hence `setScale_eq` and `divScale_eq`, with error bounds in units of the
    last place `10^(-s)`
  * exact division: `divExact_toRat`
-/
import Jimple.Decimal
import Jimple.SimpAttr

namespace Jimple

/-! ## Powers of ten -/

theorem pow10_eq_zpow (k : Int) : pow10 k = (10 : Rat) ^ k := by
  unfold pow10
  rcases k with n | n
  · simp [Rat.zpow_natCast]
  · have h : ¬ (0 ≤ Int.negSucc n) := by omega
    have h' : (-Int.negSucc n).toNat = n + 1 := by omega
    rw [ite_eq_right h, h', Rat.natCast_pow, Rat.div_def, Rat.one_mul]
    rfl

@[simp, jsimp] theorem pow10_zero : pow10 0 = 1 := rfl

@[simp, jsimp] theorem pow10_one : pow10 1 = 10 := rfl

theorem pow10_natCast (n : Nat) : pow10 n = (10 : Rat) ^ n := by
  rw [pow10_eq_zpow]; rfl

@[simp, jsimp] theorem pow10_ofNat (n : Nat) :
    pow10 (no_index (OfNat.ofNat n : Int)) = (10 : Rat) ^ n :=
  pow10_natCast n

theorem pow10_pos (k : Int) : 0 < pow10 k := by
  rw [pow10_eq_zpow]; exact Rat.zpow_pos (by decide)

theorem pow10_ne_zero (k : Int) : pow10 k ≠ 0 := Rat.ne_of_gt (pow10_pos k)

theorem pow10_add (a b : Int) : pow10 (a + b) = pow10 a * pow10 b := by
  simp only [pow10_eq_zpow]; exact Rat.zpow_add (by decide) a b

theorem pow10_neg (k : Int) : pow10 (-k) = (pow10 k)⁻¹ := by
  simp only [pow10_eq_zpow]; exact Rat.zpow_neg 10 k

@[simp, jsimp] theorem pow10_neg_ofNat (n : Nat) :
    pow10 (-(no_index (OfNat.ofNat n : Int))) = ((10 : Rat) ^ n)⁻¹ := by
  rw [pow10_neg, pow10_ofNat]

theorem pow10_mul_pow10_neg (k : Int) : pow10 k * pow10 (-k) = 1 := by
  rw [← pow10_add, Int.add_right_neg, pow10_zero]

theorem pow10_neg_mul_pow10 (k : Int) : pow10 (-k) * pow10 k = 1 := by
  rw [← pow10_add, Int.add_left_neg, pow10_zero]

theorem pow10_sub (a b : Int) : pow10 (a - b) = pow10 a / pow10 b := by
  rw [Int.sub_eq_add_neg, pow10_add, pow10_neg, Rat.div_def]

theorem pow10_succ (k : Int) : pow10 (k + 1) = pow10 k * 10 := by
  rw [pow10_add, pow10_one]

theorem one_lt_pow10 {k : Int} (h : 0 < k) : 1 < pow10 k := by
  unfold pow10
  rw [ite_eq_left (by omega)]
  have : 1 < 10 ^ k.toNat := Nat.one_lt_pow (by omega) (by decide)
  exact Rat.natCast_lt_natCast.mpr this

theorem pow10_lt_pow10 {a b : Int} (h : a < b) : pow10 a < pow10 b := by
  rw [show b = a + (b - a) by omega, pow10_add]
  have := Rat.mul_lt_mul_of_pos_left (one_lt_pow10 (show 0 < b - a by omega)) (pow10_pos a)
  rwa [Rat.mul_one] at this

theorem pow10_le_pow10 {a b : Int} (h : a ≤ b) : pow10 a ≤ pow10 b := by
  rcases Int.lt_or_eq_of_le h with h | h
  · exact Rat.le_of_lt (pow10_lt_pow10 h)
  · rw [h]; exact Rat.le_refl

/-- `pow10Int` is `pow10` on natural exponents. -/
@[simp, jsimp] theorem pow10Int_cast (n : Nat) : ((pow10Int n : Int) : Rat) = pow10 n := by
  simp [pow10Int, pow10_natCast]

theorem pow10Int_cast_toNat {k : Int} (h : 0 ≤ k) : ((pow10Int k.toNat : Int) : Rat) = pow10 k := by
  rw [pow10Int_cast, Int.toNat_of_nonneg h]

theorem pow10Int_pos (n : Nat) : 0 < pow10Int n := by
  have := pow10_pos n
  rw [← pow10Int_cast] at this
  exact Rat.intCast_pos.mp this

theorem pow10Int_ne_zero (n : Nat) : pow10Int n ≠ 0 := by
  have := pow10Int_pos n; omega

private theorem rat_mul_pow (a b : Rat) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, ih]; grind

theorem pow10_mul_natCast (k : Int) (n : Nat) : pow10 (k * n) = pow10 k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show k * ((n + 1 : Nat) : Int) = k * n + k by push_cast; grind, pow10_add, ih, Rat.pow_succ]

theorem pow10_trailingZeros_dvd (n : Nat) : 10 ^ trailingZeros n ∣ n := by
  induction n using trailingZeros.induct with
  | case1 n h _ ih =>
    rw [trailingZeros, dite_eq_left h, Nat.pow_succ]
    have := Nat.mul_dvd_mul_right ih 10
    rwa [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)] at this
  | case2 n h =>
    rw [trailingZeros, dite_eq_right h]; exact Nat.one_dvd n

/-! ## Values -/

namespace BigDec

theorem toRat_def (d : BigDec) : d.toRat = d.unscaled * pow10 (-d.scale) := rfl

@[simp, jsimp] theorem toRat_mk (u s : Int) : (⟨u, s⟩ : BigDec).toRat = u * pow10 (-s) := rfl

/-- The unscaled value after rescaling up to scale `s`, in `Rat`. -/
theorem upscale_cast {d : BigDec} {s : Int} (h : d.scale ≤ s) :
    ((d.upscale s : Int) : Rat) = d.toRat * pow10 s := by
  unfold upscale toRat
  rw [Rat.intCast_mul, pow10Int_cast_toNat (by omega), show s - d.scale = -d.scale + s by omega,
    pow10_add, Rat.mul_assoc]

/-- Rescaling up preserves the value. -/
@[simp high, jsimp high] theorem toRat_upscale {d : BigDec} {s : Int} (h : d.scale ≤ s) :
    (⟨d.upscale s, s⟩ : BigDec).toRat = d.toRat := by
  rw [toRat_mk, upscale_cast h, Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one]

@[simp, jsimp] theorem toRat_add (x y : BigDec) : (x.add y).toRat = x.toRat + y.toRat := by
  unfold add
  simp only [toRat_mk, Rat.intCast_add, upscale_cast (Int.le_max_left x.scale y.scale),
    upscale_cast (Int.le_max_right x.scale y.scale)]
  rw [Rat.add_mul, Rat.mul_assoc, Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one, Rat.mul_one]

@[simp, jsimp] theorem toRat_negate (x : BigDec) : x.negate.toRat = -x.toRat := by
  simp only [negate, Rat.intCast_neg, Rat.neg_mul, toRat_def]

@[simp, jsimp] theorem toRat_sub (x y : BigDec) : (x.sub y).toRat = x.toRat - y.toRat := by
  rw [sub, toRat_add, toRat_negate, Rat.sub_eq_add_neg]

@[simp, jsimp] theorem toRat_mul (x y : BigDec) : (x.mul y).toRat = x.toRat * y.toRat := by
  simp only [mul, toRat_def, Rat.intCast_mul, Int.neg_add, pow10_add]
  grind

@[simp high, jsimp high] theorem toRat_mk_zero (i : Int) : (⟨i, 0⟩ : BigDec).toRat = i := by
  simp

@[simp, jsimp] theorem toRat_ofInt (i : Int) : (ofInt i).toRat = i := toRat_mk_zero i

@[simp, jsimp] theorem toRat_zero : zero.toRat = 0 := by simp [zero]
@[simp, jsimp] theorem toRat_one : one.toRat = 1 := by simp [one]
@[simp, jsimp] theorem toRat_ten : ten.toRat = 10 := by simp [ten]

@[simp, jsimp] theorem toRat_abs (x : BigDec) : x.abs.toRat = x.toRat.abs := by
  simp only [abs, toRat_def]
  by_cases h : 0 ≤ x.unscaled
  · rw [Int.natAbs_of_nonneg h, Rat.abs_of_nonneg
      (Rat.mul_nonneg (Rat.intCast_nonneg.mpr h) (Rat.le_of_lt (pow10_pos _)))]
  · rw [Int.ofNat_natAbs_of_nonpos (by omega), Rat.abs_of_nonpos, Rat.intCast_neg, Rat.neg_mul]
    exact Rat.le_of_lt ((Rat.mul_neg_iff_of_pos_right (pow10_pos _)).mpr
      (Rat.intCast_neg_iff.mpr (by omega)))

@[simp, jsimp] theorem toRat_scaleByPowerOfTen (x : BigDec) (n : Int) :
    (x.scaleByPowerOfTen n).toRat = x.toRat * pow10 n := by
  simp only [scaleByPowerOfTen, toRat_def]
  rw [show -(x.scale - n) = -x.scale + n by omega, pow10_add, Rat.mul_assoc]

@[simp, jsimp] theorem toRat_movePointLeft (x : BigDec) (n : Int) :
    (x.movePointLeft n).toRat = x.toRat * pow10 (-n) := by
  have hv : (⟨x.unscaled, x.scale + n⟩ : BigDec).toRat = x.toRat * pow10 (-n) := by
    simp only [toRat_def]; rw [Int.neg_add, pow10_add, Rat.mul_assoc]
  unfold movePointLeft
  simp only []
  split
  · rename_i h
    rw [toRat_upscale (Int.le_of_lt h), hv]
  · exact hv

@[simp, jsimp] theorem toRat_movePointRight (x : BigDec) (n : Int) :
    (x.movePointRight n).toRat = x.toRat * pow10 n := by
  rw [movePointRight, toRat_movePointLeft, Int.neg_neg]

@[simp, jsimp] theorem toRat_stripTrailingZeros (x : BigDec) :
    x.stripTrailingZeros.toRat = x.toRat := by
  unfold stripTrailingZeros
  split
  · rename_i h; simp [toRat_def, h, zero]
  · simp only []
    have hdvd : pow10Int (trailingZeros x.unscaled.natAbs) ∣ x.unscaled := by
      have := Int.ofNat_dvd_left.mpr (pow10_trailingZeros_dvd x.unscaled.natAbs)
      simpa [pow10Int, Int.natCast_pow] using this
    generalize trailingZeros x.unscaled.natAbs = t at hdvd ⊢
    obtain ⟨k, hk⟩ := hdvd
    rw [toRat_mk, toRat_def, hk, Int.mul_ediv_cancel_left _ (pow10Int_ne_zero t), Rat.intCast_mul,
      pow10Int_cast, show -(x.scale - (t : Int)) = (t : Int) + -x.scale by omega, pow10_add]
    grind

/-- `pow(n)` is the power of the value. -/
theorem pow_toRat {x z : BigDec} {n : Int} (h : x.pow n = some z) :
    z.toRat = x.toRat ^ n.toNat := by
  unfold BigDec.pow at h
  split at h
  · simp at h
  · cases h
    have hn0 : 0 ≤ n := by omega
    rw [toRat_mk, toRat_def, Rat.intCast_pow, rat_mul_pow, ← pow10_mul_natCast,
      Int.toNat_of_nonneg hn0, Int.neg_mul]

/-- `toBigInteger()` truncates the value toward zero. -/
theorem toBigInt_eq (x : BigDec) : x.toBigInt = ratTrunc x.toRat := rfl

theorem toRat_eq_zero_iff (x : BigDec) : x.toRat = 0 ↔ x.unscaled = 0 := by
  rw [toRat_def, Rat.mul_eq_zero, Rat.intCast_eq_zero_iff]
  have := pow10_ne_zero (-x.scale)
  constructor
  · intro h; rcases h with h | h
    · exact h
    · exact absurd h this
  · intro h; exact Or.inl h

theorem toRat_pos_iff (x : BigDec) : 0 < x.toRat ↔ 0 < x.unscaled := by
  rw [toRat_def, Rat.mul_pos_iff_of_pos_right (pow10_pos _), Rat.intCast_pos]

theorem toRat_neg_iff (x : BigDec) : x.toRat < 0 ↔ x.unscaled < 0 := by
  rw [toRat_def, Rat.mul_neg_iff_of_pos_right (pow10_pos _), Rat.intCast_neg_iff]

/-! ### Comparison -/

private theorem rat_mul_right_inj {a b c : Rat} (hc : c ≠ 0) : a * c = b * c ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· / c) h
    simpa only [Rat.mul_div_cancel hc] using this
  · intro h; rw [h]

/-- `compareTo` is the comparison of the values. -/
theorem compareTo_eq (x y : BigDec) :
    x.compareTo y = if x.toRat < y.toRat then -1 else if x.toRat = y.toRat then 0 else 1 := by
  have hx := upscale_cast (d := x) (Int.le_max_left x.scale y.scale)
  have hy := upscale_cast (d := y) (Int.le_max_right x.scale y.scale)
  have hlt : x.upscale (Max.max x.scale y.scale) < y.upscale (Max.max x.scale y.scale) ↔
      x.toRat < y.toRat := by
    rw [← Rat.intCast_lt_intCast, hx, hy]; exact Rat.mul_lt_mul_right (pow10_pos _)
  have heq : x.upscale (Max.max x.scale y.scale) = y.upscale (Max.max x.scale y.scale) ↔
      x.toRat = y.toRat := by
    rw [← Rat.intCast_inj, hx, hy]; exact rat_mul_right_inj (pow10_ne_zero _)
  unfold compareTo
  simp only [hlt, heq]

@[simp, jsimp] theorem compareTo_lt_zero_iff (x y : BigDec) :
    x.compareTo y < 0 ↔ x.toRat < y.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2]

@[simp, jsimp] theorem compareTo_le_zero_iff (x y : BigDec) :
    x.compareTo y ≤ 0 ↔ x.toRat ≤ y.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2] <;> grind

@[simp, jsimp] theorem compareTo_pos_iff (x y : BigDec) :
    0 < x.compareTo y ↔ y.toRat < x.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2] <;> grind

@[simp, jsimp] theorem compareTo_nonneg_iff (x y : BigDec) :
    0 ≤ x.compareTo y ↔ y.toRat ≤ x.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2] <;> grind

@[simp, jsimp] theorem compareTo_eq_zero_iff (x y : BigDec) :
    x.compareTo y = 0 ↔ x.toRat = y.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2] <;> grind

theorem compareTo_eq_neg_one_iff (x y : BigDec) : x.compareTo y = -1 ↔ x.toRat < y.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2]

theorem compareTo_eq_one_iff (x y : BigDec) : x.compareTo y = 1 ↔ y.toRat < x.toRat := by
  rw [compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;> simp [h1, h2] <;> grind

theorem compareTo_swap (x y : BigDec) : y.compareTo x = -x.compareTo y := by
  rw [compareTo_eq, compareTo_eq]
  by_cases h1 : x.toRat < y.toRat <;> by_cases h2 : x.toRat = y.toRat <;>
    by_cases h3 : y.toRat < x.toRat <;> simp [h1, h2, h3] <;> grind

@[simp, jsimp] theorem compareTo_self (x : BigDec) : x.compareTo x = 0 :=
  (compareTo_eq_zero_iff x x).mpr rfl

/-- Equal decimals compare equal. -/
theorem compareTo_of_eq {x y : BigDec} (h : x = y) : x.compareTo y = 0 := by
  rw [h, compareTo_self]

/-- `equals` (structural equality) sees the scale, `compareTo` does not. -/
theorem eq_iff {x y : BigDec} : x = y ↔ x.unscaled = y.unscaled ∧ x.scale = y.scale := by
  cases x; cases y; simp

/-- Rescaling up gives a decimal that compares equal (e.g. `2.0` and `2.00`). -/
theorem compareTo_upscale {x : BigDec} {s : Int} (h : x.scale ≤ s) :
    (⟨x.upscale s, s⟩ : BigDec).compareTo x = 0 := by
  rw [compareTo_eq_zero_iff, toRat_upscale h]

/-- `2.0` and `2.00` are different (`equals` is false) but compare equal. -/
theorem compareTo_two_scales : (⟨20, 1⟩ : BigDec).compareTo ⟨200, 2⟩ = 0 ∧
    (⟨20, 1⟩ : BigDec) ≠ ⟨200, 2⟩ := by decide

theorem signum_eq (x : BigDec) :
    x.signum = if 0 < x.toRat then 1 else if x.toRat < 0 then -1 else 0 := by
  simp only [signum, GT.gt, toRat_pos_iff, toRat_neg_iff]

theorem max_eq (x y : BigDec) : x.max y = if y.toRat ≤ x.toRat then x else y := by
  simp only [BigDec.max, GE.ge, compareTo_nonneg_iff]

theorem min_eq (x y : BigDec) : x.min y = if x.toRat ≤ y.toRat then x else y := by
  simp only [BigDec.min, compareTo_le_zero_iff]

@[simp, jsimp] theorem toRat_max (x y : BigDec) : (x.max y).toRat = Max.max x.toRat y.toRat := by
  rw [max_eq, Rat.max_def]
  by_cases h1 : y.toRat ≤ x.toRat <;> by_cases h2 : x.toRat ≤ y.toRat <;> simp [h1, h2] <;> grind

@[simp, jsimp] theorem toRat_min (x y : BigDec) : (x.min y).toRat = Min.min x.toRat y.toRat := by
  rw [min_eq, Rat.min_def]
  split <;> rfl

end BigDec

/-! ## Rounding in `Rat` -/

/-- Rounding a rational number to an integer as `java.math.RoundingMode` specifies; the
    specification that `divRound`, and so `setScale` and `divide(divisor, scale, mode)`,
    implement (`divRound_eq`, `BigDec.setScale_eq`, `BigDec.divScale_eq`).
    `none` exactly when `UNNECESSARY` meets a non-integer. -/
def roundRat (rm : RoundingMode) (q : Rat) : Option Int :=
  -- the neighbours away from zero and toward zero, and the even neighbour
  let up : Int := if 0 ≤ q then q.ceil else q.floor
  let down : Int := ratTrunc q
  let even : Int := if q.floor % 2 = 0 then q.floor else q.ceil
  -- the nearest integer, or `tie` when `q` is exactly halfway between two integers
  let nearest (tie : Int) : Int :=
    if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil else tie
  match rm with
  | .UP => some up
  | .DOWN => some down
  | .CEILING => some q.ceil
  | .FLOOR => some q.floor
  | .HALF_UP => some (nearest up)
  | .HALF_DOWN => some (nearest down)
  | .HALF_EVEN => some (nearest even)
  | .UNNECESSARY => if (q.floor : Rat) = q then some q.floor else none

section roundRat
variable (q : Rat)

theorem roundRat_UP : roundRat .UP q = some (if 0 ≤ q then q.ceil else q.floor) := rfl
theorem roundRat_DOWN : roundRat .DOWN q = some (ratTrunc q) := rfl
theorem roundRat_CEILING : roundRat .CEILING q = some q.ceil := rfl
theorem roundRat_FLOOR : roundRat .FLOOR q = some q.floor := rfl
theorem roundRat_HALF_UP : roundRat .HALF_UP q =
    some (if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else if 0 ≤ q then q.ceil else q.floor) := rfl
theorem roundRat_HALF_DOWN : roundRat .HALF_DOWN q =
    some (if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else ratTrunc q) := rfl
theorem roundRat_HALF_EVEN : roundRat .HALF_EVEN q =
    some (if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil
      else if q.floor % 2 = 0 then q.floor else q.ceil) := rfl
theorem roundRat_UNNECESSARY : roundRat .UNNECESSARY q =
    if (q.floor : Rat) = q then some q.floor else none := rfl

end roundRat

theorem floor_eq_of_le_of_lt {x : Rat} {z : Int} (h1 : (z : Rat) ≤ x) (h2 : x < z + 1) :
    x.floor = z := by
  have a : z ≤ x.floor := Rat.le_floor_iff.mpr h1
  have b : x.floor < z + 1 := Rat.floor_lt_iff.mpr (by push_cast; exact h2)
  omega

theorem ceil_eq_of_lt_of_le {x : Rat} {z : Int} (h1 : (z : Rat) - 1 < x) (h2 : x ≤ z) :
    x.ceil = z := by
  have a : x.ceil ≤ z := Rat.ceil_le_iff.mpr h2
  have b : z - 1 < x.ceil := Rat.lt_ceil_iff.mpr (by push_cast; exact h1)
  omega

/-- What the rounding proofs need to know about `floor` and `ceil`. -/
theorem floor_ceil_facts (q : Rat) :
    (q.floor : Rat) ≤ q ∧ q < q.floor + 1 ∧ q ≤ q.ceil ∧ (q.ceil : Rat) < q + 1 ∧
    (q.ceil : Rat) ≤ q.floor + 1 ∧ (0 ≤ q → (0 : Rat) ≤ q.floor) ∧
    (q ≤ 0 → (q.ceil : Rat) ≤ 0) := by
  have h1 := Rat.floor_le q
  have h2 := Rat.lt_floor_add_one q
  have h3 := Rat.le_ceil (x := q)
  have h4 := Rat.ceil_lt (x := q)
  push_cast at h2
  have h5 : q.ceil ≤ q.floor + 1 := by
    have : (q.ceil : Rat) < ((q.floor + 1 + 1 : Int) : Rat) := by push_cast; grind
    have := Rat.intCast_lt_intCast.mp this
    omega
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · have := Rat.intCast_le_intCast.mpr h5; push_cast at this; exact this
  · intro h
    have : (0 : Int) ≤ q.floor := Rat.le_floor_iff.mpr (by simpa using h)
    exact Rat.intCast_nonneg.mpr this
  · intro h
    have : q.ceil ≤ (0 : Int) := Rat.ceil_le_iff.mpr (by simpa using h)
    exact Rat.intCast_nonpos.mpr this

/-- An integer rounds to itself in every mode. -/
@[simp, jsimp] theorem roundRat_intCast (rm : RoundingMode) (k : Int) : roundRat rm k = some k := by
  have hf : (k : Rat).floor = k := Rat.floor_intCast k
  have hc : (k : Rat).ceil = k := Rat.ceil_intCast k
  have ht : ratTrunc k = k := by unfold ratTrunc; split <;> simp [hf, hc]
  have h0 : (k : Rat) - k < 1/2 := by grind
  cases rm <;> simp [roundRat, hf, hc, ht, h0]

/-- Every mode rounds to one of the two neighbouring integers. -/
theorem roundRat_floor_or_ceil {rm : RoundingMode} {q : Rat} {r : Int}
    (h : roundRat rm q = some r) : r = q.floor ∨ r = q.ceil := by
  cases rm <;> simp only [roundRat, Option.some.injEq, ratTrunc] at h <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    simp_all

/-- Rounding is total except for `UNNECESSARY`. -/
theorem roundRat_isSome {rm : RoundingMode} (hrm : rm ≠ .UNNECESSARY) (q : Rat) :
    (roundRat rm q).isSome := by
  cases rm <;> simp_all [roundRat]

theorem roundRat_UNNECESSARY_eq_some {q : Rat} {r : Int} :
    roundRat .UNNECESSARY q = some r ↔ q = r := by
  rw [roundRat_UNNECESSARY]
  constructor
  · intro h; split at h
    · simp only [Option.some.injEq] at h; subst h; rename_i h'; exact h'.symm
    · simp at h
  · intro h; subst h; simp

theorem roundRat_UNNECESSARY_eq_none {q : Rat} :
    roundRat .UNNECESSARY q = none ↔ ∀ k : Int, q ≠ k := by
  rw [roundRat_UNNECESSARY]
  constructor
  · intro h k hk; subst hk; simp at h
  · intro h; split
    · rename_i h'; exact absurd h'.symm (h _)
    · rfl

/-! ### Error bounds -/

section bounds
variable {q : Rat} {r : Int}

theorem roundRat_FLOOR_bounds (h : roundRat .FLOOR q = some r) : (r : Rat) ≤ q ∧ q < r + 1 := by
  simp only [roundRat_FLOOR, Option.some.injEq] at h; subst h
  have := floor_ceil_facts q; grind

theorem roundRat_CEILING_bounds (h : roundRat .CEILING q = some r) : (r : Rat) - 1 < q ∧ q ≤ r := by
  simp only [roundRat_CEILING, Option.some.injEq] at h; subst h
  have := floor_ceil_facts q; grind

/-- `DOWN` (truncation) never increases the magnitude, and loses less than one. -/
theorem roundRat_DOWN_bounds (h : roundRat .DOWN q = some r) :
    (r : Rat).abs ≤ q.abs ∧ q.abs - 1 < (r : Rat).abs := by
  simp only [roundRat_DOWN, ratTrunc, Option.some.injEq] at h; subst h
  have := floor_ceil_facts q
  simp only [Rat.abs]; split <;> grind

/-- `UP` never decreases the magnitude, and adds less than one. -/
theorem roundRat_UP_bounds (h : roundRat .UP q = some r) :
    q.abs ≤ (r : Rat).abs ∧ (r : Rat).abs < q.abs + 1 := by
  simp only [roundRat_UP, Option.some.injEq] at h; subst h
  have := floor_ceil_facts q
  simp only [Rat.abs]; split <;> grind

private theorem nearest_bound (q : Rat) (t : Int) (ht : t = q.floor ∨ t = q.ceil) :
    (q - ((if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil else t : Int)
      : Rat)).abs ≤ 1/2 := by
  have := floor_ceil_facts q
  simp only [Rat.abs]
  rcases ht with ht | ht <;> subst ht <;> split <;> (try split) <;> grind

theorem roundRat_HALF_UP_bound (h : roundRat .HALF_UP q = some r) : (q - r).abs ≤ 1/2 := by
  simp only [roundRat_HALF_UP, Option.some.injEq] at h; subst h
  exact nearest_bound q _ (by split <;> simp)

theorem roundRat_HALF_DOWN_bound (h : roundRat .HALF_DOWN q = some r) : (q - r).abs ≤ 1/2 := by
  simp only [roundRat_HALF_DOWN, Option.some.injEq] at h; subst h
  exact nearest_bound q _ (by unfold ratTrunc; split <;> simp)

theorem roundRat_HALF_EVEN_bound (h : roundRat .HALF_EVEN q = some r) : (q - r).abs ≤ 1/2 := by
  simp only [roundRat_HALF_EVEN, Option.some.injEq] at h; subst h
  exact nearest_bound q _ (by split <;> simp)

private theorem nearest_le (q : Rat) (t : Int) (ht : t = q.floor ∨ t = q.ceil) (k : Int) :
    (q - ((if q - q.floor < 1/2 then q.floor else if q.ceil - q < 1/2 then q.ceil else t : Int)
      : Rat)).abs ≤ (q - k).abs := by
  have hf := floor_ceil_facts q
  have h5 : q.ceil ≤ q.floor + 1 := by
    have : (q.ceil : Rat) ≤ ((q.floor + 1 : Int) : Rat) := by push_cast; exact hf.2.2.2.2.1
    exact Rat.intCast_le_intCast.mp this
  have h6 : q.floor ≤ q.ceil := Rat.intCast_le_intCast.mp (Rat.le_trans hf.1 hf.2.2.1)
  have hk : (k : Rat) ≤ q.floor ∨ (q.ceil : Rat) ≤ k := by
    by_cases h : k ≤ q.floor
    · exact Or.inl (Rat.intCast_le_intCast.mpr h)
    · exact Or.inr (Rat.intCast_le_intCast.mpr (by omega))
  have hcf : (q.ceil : Rat) = q.floor ∨ (q.ceil : Rat) = q.floor + 1 := by
    rcases (show q.ceil = q.floor ∨ q.ceil = q.floor + 1 by omega) with h | h
    · left; rw [h]
    · right; rw [h]; push_cast; rfl
  simp only [Rat.abs]
  rcases ht with ht | ht <;> subst ht <;> split <;> (try split) <;> grind

/-- The `HALF_*` modes round to a nearest integer. -/
theorem roundRat_half_nearest {rm : RoundingMode}
    (hrm : rm = .HALF_UP ∨ rm = .HALF_DOWN ∨ rm = .HALF_EVEN) (h : roundRat rm q = some r)
    (k : Int) : (q - r).abs ≤ (q - k).abs := by
  rcases hrm with rfl | rfl | rfl
  · simp only [roundRat_HALF_UP, Option.some.injEq] at h; subst h
    exact nearest_le q _ (by split <;> simp) k
  · simp only [roundRat_HALF_DOWN, Option.some.injEq] at h; subst h
    exact nearest_le q _ (by unfold ratTrunc; split <;> simp) k
  · simp only [roundRat_HALF_EVEN, Option.some.injEq] at h; subst h
    exact nearest_le q _ (by split <;> simp) k

theorem roundRat_UNNECESSARY_exact (h : roundRat .UNNECESSARY q = some r) : q = r :=
  roundRat_UNNECESSARY_eq_some.mp h

/-- Every mode moves by less than one. -/
theorem roundRat_bound {rm : RoundingMode} (h : roundRat rm q = some r) : (q - r).abs < 1 := by
  have := floor_ceil_facts q
  simp only [Rat.abs]
  rcases roundRat_floor_or_ceil h with h' | h' <;> subst h' <;> split <;> grind

end bounds

/-! ## `divRound` rounds the exact quotient -/

section divRound

private theorem div_lt_half_iff {r d : Int} (hd : 0 < d) : (r : Rat) / d < 1/2 ↔ 2 * r < d := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.mpr hd
  rw [Rat.div_lt_iff hdR, ← Rat.intCast_lt_intCast, Rat.intCast_mul]
  simp only [Rat.intCast_ofNat]
  constructor <;> intro h <;> grind

private theorem half_lt_div_iff {r d : Int} (hd : 0 < d) : 1/2 < (r : Rat) / d ↔ d < 2 * r := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.mpr hd
  rw [Rat.lt_div_iff hdR, ← Rat.intCast_lt_intCast, Rat.intCast_mul]
  simp only [Rat.intCast_ofNat]
  constructor <;> intro h <;> grind

private theorem div_lt_neg_half_iff {r d : Int} (hd : 0 < d) :
    (r : Rat) / d < -1/2 ↔ 2 * r < -d := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.mpr hd
  rw [Rat.div_lt_iff hdR, ← Rat.intCast_lt_intCast, Rat.intCast_mul, Rat.intCast_neg]
  simp only [Rat.intCast_ofNat]
  constructor <;> intro h <;> grind

private theorem neg_half_lt_div_iff {r d : Int} (hd : 0 < d) :
    -1/2 < (r : Rat) / d ↔ -d < 2 * r := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.mpr hd
  rw [Rat.lt_div_iff hdR, ← Rat.intCast_lt_intCast, Rat.intCast_mul, Rat.intCast_neg]
  simp only [Rat.intCast_ofNat]
  constructor <;> intro h <;> grind

theorem divRound_eq_of_pos (n d : Int) (hd : 0 < d) (rm : RoundingMode) :
    divRound n d rm = roundRat rm ((n : Rat) / d) := by
  have hdR : (0 : Rat) < d := Rat.intCast_pos.mpr hd
  have hdne : (d : Rat) ≠ 0 := Rat.ne_of_gt hdR
  have key : n.tmod d + d * n.tdiv d = n := Int.tmod_add_mul_tdiv n d
  have hr_lt : n.tmod d < d := Int.tmod_lt_of_pos n hd
  have hr_gt : -d < n.tmod d := Int.lt_tmod_of_pos n hd
  have hr_nonneg : 0 ≤ n → 0 ≤ n.tmod d := Int.tmod_nonneg d
  have hr_nonpos : n ≤ 0 → n.tmod d ≤ 0 := fun h => by
    have := Int.tmod_nonneg d (show 0 ≤ -n by omega); rw [Int.neg_tmod] at this; omega
  have hq_nonneg : 0 ≤ n → 0 ≤ n.tdiv d := fun h => Int.tdiv_nonneg h (Int.le_of_lt hd)
  have hq_nonpos : n ≤ 0 → n.tdiv d ≤ 0 := fun h => by
    have := Int.tdiv_nonneg (show 0 ≤ -n by omega) (Int.le_of_lt hd)
    rw [Int.neg_tdiv] at this; omega
  unfold divRound
  simp only []
  generalize n.tdiv d = q at *
  generalize n.tmod d = r at *
  have hX : (n : Rat) / d = q + (r : Rat) / d := by
    have : (n : Rat) = r + d * q := by rw [← key]; push_cast; rfl
    rw [this]; grind
  rw [hX]
  by_cases hr0 : r = 0
  · subst hr0
    rw [ite_eq_left rfl]
    have : (q : Rat) + ((0 : Int) : Rat) / d = q := by simp [Rat.div_def, Rat.add_zero]
    rw [this, roundRat_intCast]
  rw [ite_eq_right hr0]
  rcases Int.lt_or_gt_of_ne hr0 with hneg | hpos
  · -- `r < 0`: then `n < 0`, the quotient lies in `(q - 1, q)`
    have hn : n < 0 := by
      rcases Int.lt_or_le n 0 with h | h
      · exact h
      · exact absurd (hr_nonneg h) (by omega)
    have hs : ¬ ((n < 0) = (d < 0)) := by
      intro h; have : d < 0 := h ▸ hn; omega
    rw [ite_eq_right hs]
    have hq0 : q ≤ 0 := hq_nonpos (Int.le_of_lt hn)
    have hF1 : (r : Rat) / d < 0 := by
      rw [Rat.div_lt_iff hdR, Rat.zero_mul]; exact Rat.intCast_neg_iff.mpr hneg
    have hF2 : -1 < (r : Rat) / d := by
      rw [Rat.lt_div_iff hdR]
      have : ((-d : Int) : Rat) < r := Rat.intCast_lt_intCast.mpr hr_gt
      push_cast at this; grind
    have hqR : (q : Rat) ≤ 0 := Rat.intCast_nonpos.mpr hq0
    have hfl : ((q : Rat) + r / d).floor = q - 1 :=
      floor_eq_of_le_of_lt (by push_cast; grind) (by push_cast; grind)
    have hce : ((q : Rat) + r / d).ceil = q := ceil_eq_of_lt_of_le (by grind) (by grind)
    have hX0 : ¬ (0 ≤ (q : Rat) + r / d) := by grind
    have ht : ratTrunc ((q : Rat) + r / d) = q := by rw [ratTrunc, ite_eq_right hX0, hce]
    have c1 : (q : Rat) + r / d - ((q - 1 : Int) : Rat) < 1/2 ↔ 2 * r < -d := by
      rw [← div_lt_neg_half_iff hd]; push_cast; constructor <;> intro h <;> grind
    have c2 : ((q : Int) : Rat) - ((q : Rat) + r / d) < 1/2 ↔ -d < 2 * r := by
      rw [← neg_half_lt_div_iff hd]; constructor <;> intro h <;> grind
    cases rm
    · simp only [roundRat_UP, ite_eq_right hX0, hfl]; congr 1 <;> omega
    · simp only [roundRat_DOWN, ht]
    · simp only [roundRat_CEILING, hce]; rfl
    · simp only [roundRat_FLOOR, hfl]; rfl
    · simp only [roundRat_HALF_UP, hfl, hce, c1, c2, ite_eq_right hX0]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_HALF_DOWN, hfl, hce, c1, c2, ht]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_HALF_EVEN, hfl, hce, c1, c2]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_UNNECESSARY, hfl]
      rw [ite_eq_right]
      push_cast; intro h; grind
  · -- `r > 0`: then `n > 0`, the quotient lies in `(q, q + 1)`
    have hn : 0 < n := by
      rcases Int.lt_or_le 0 n with h | h
      · exact h
      · exact absurd (hr_nonpos h) (by omega)
    have hs : (n < 0) = (d < 0) :=
      propext ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    rw [ite_eq_left hs]
    have hq0 : 0 ≤ q := hq_nonneg (Int.le_of_lt hn)
    have hF1 : 0 < (r : Rat) / d := by
      rw [Rat.lt_div_iff hdR, Rat.zero_mul]; exact Rat.intCast_pos.mpr hpos
    have hF2 : (r : Rat) / d < 1 := by
      rw [Rat.div_lt_iff hdR, Rat.one_mul]; exact Rat.intCast_lt_intCast.mpr hr_lt
    have hqR : (0 : Rat) ≤ q := Rat.intCast_nonneg.mpr hq0
    have hfl : ((q : Rat) + r / d).floor = q := floor_eq_of_le_of_lt (by grind) (by grind)
    have hce : ((q : Rat) + r / d).ceil = q + 1 :=
      ceil_eq_of_lt_of_le (by push_cast; grind) (by push_cast; grind)
    have hX0 : 0 ≤ (q : Rat) + r / d := by grind
    have ht : ratTrunc ((q : Rat) + r / d) = q := by rw [ratTrunc, ite_eq_left hX0, hfl]
    have c1 : (q : Rat) + r / d - (q : Rat) < 1/2 ↔ 2 * r < d := by
      rw [← div_lt_half_iff hd]; constructor <;> intro h <;> grind
    have c2 : ((q + 1 : Int) : Rat) - ((q : Rat) + r / d) < 1/2 ↔ d < 2 * r := by
      rw [← half_lt_div_iff hd]; push_cast; constructor <;> intro h <;> grind
    cases rm
    · simp only [roundRat_UP, ite_eq_left hX0, hce]
    · simp only [roundRat_DOWN, ht]
    · simp only [roundRat_CEILING, hce]; rfl
    · simp only [roundRat_FLOOR, hfl]; rfl
    · simp only [roundRat_HALF_UP, hfl, hce, c1, c2, ite_eq_left hX0]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_HALF_DOWN, hfl, hce, c1, c2, ht]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_HALF_EVEN, hfl, hce, c1, c2]
      repeat' split
      all_goals first | rfl | (simp only [Option.some.injEq]; omega)
    · simp only [roundRat_UNNECESSARY, hfl]
      rw [ite_eq_right]
      intro h; grind

/-- `divRound` only sees the signs of `n` and `d` through their quotient. -/
theorem divRound_neg_neg (n d : Int) (hd : d ≠ 0) (rm : RoundingMode) :
    divRound (-n) (-d) rm = divRound n d rm := by
  unfold divRound
  simp only [Int.neg_tdiv_neg, Int.tmod_neg, Int.neg_tmod, Int.neg_eq_zero, Int.natAbs_neg]
  by_cases hr : n.tmod d = 0
  · simp only [hr, ite_true]
  · rw [ite_eq_right hr, ite_eq_right hr]
    have hn : n ≠ 0 := by intro h; subst h; simp at hr
    by_cases hs : (n < 0) = (d < 0)
    · have hs' : (-n < 0) = (-d < 0) := propext (by have := Iff.of_eq hs; omega)
      rw [ite_eq_left hs, ite_eq_left hs']
    · have hs' : ¬ ((-n < 0) = (-d < 0)) := fun h => hs (propext (by have := Iff.of_eq h; omega))
      rw [ite_eq_right hs, ite_eq_right hs']

/-- `divRound n d rm` is `roundRat rm` of the exact quotient `n / d`. -/
theorem divRound_eq (n d : Int) (hd : d ≠ 0) (rm : RoundingMode) :
    divRound n d rm = roundRat rm ((n : Rat) / d) := by
  rcases Int.lt_or_gt_of_ne hd with h | h
  · rw [← divRound_neg_neg n d hd, divRound_eq_of_pos (-n) (-d) (by omega)]
    congr 1; push_cast; grind
  · exact divRound_eq_of_pos n d h rm

end divRound

/-! ## `setScale` and `divide(divisor, scale, mode)` -/

namespace BigDec

/-- `x.setScale s rm` rounds `x * 10^s` to an integer `r` and returns `r × 10^(-s)`. -/
theorem setScale_eq (x : BigDec) (s : Int) (rm : RoundingMode) :
    x.setScale s rm = (roundRat rm (x.toRat * pow10 s)).map (fun r => ⟨r, s⟩) := by
  unfold setScale
  split
  · rename_i h
    rw [← upscale_cast h, roundRat_intCast]; rfl
  · rename_i h
    rw [divRound_eq _ _ (pow10Int_ne_zero _), pow10Int_cast_toNat (by omega)]
    congr 2
    rw [toRat_def, Rat.div_def, ← pow10_neg, Rat.mul_assoc, ← pow10_add]
    congr 2; omega

theorem setScale_eq_some {x z : BigDec} {s : Int} {rm : RoundingMode} :
    x.setScale s rm = some z ↔ ∃ r, roundRat rm (x.toRat * pow10 s) = some r ∧ z = ⟨r, s⟩ := by
  rw [setScale_eq]
  cases roundRat rm (x.toRat * pow10 s) <;> simp [eq_comm]

/-- The value of a `setScale` result, through the rounded integer `r`. -/
theorem setScale_toRat {x z : BigDec} {s r : Int} {rm : RoundingMode}
    (h : x.setScale s rm = some z) (hr : roundRat rm (x.toRat * pow10 s) = some r) :
    z.toRat = r * pow10 (-s) := by
  rw [setScale_eq, hr] at h; cases h; rfl

theorem setScale_scale {x z : BigDec} {s : Int} {rm : RoundingMode}
    (h : x.setScale s rm = some z) : z.scale = s := by
  obtain ⟨r, -, rfl⟩ := setScale_eq_some.mp h; rfl

/-- Increasing the scale is exact. -/
theorem setScale_of_le {x : BigDec} {s : Int} (h : x.scale ≤ s) (rm : RoundingMode) :
    x.setScale s rm = some ⟨x.upscale s, s⟩ := by
  unfold setScale; rw [ite_eq_left h]

theorem setScale_toRat_of_le {x z : BigDec} {s : Int} {rm : RoundingMode} (h : x.scale ≤ s)
    (hz : x.setScale s rm = some z) : z.toRat = x.toRat := by
  rw [setScale_of_le h] at hz; cases hz; exact toRat_upscale h

theorem setScale_isSome {rm : RoundingMode} (hrm : rm ≠ .UNNECESSARY) (x : BigDec) (s : Int) :
    (x.setScale s rm).isSome := by
  rw [setScale_eq]
  have := roundRat_isSome hrm (x.toRat * pow10 s)
  revert this; cases roundRat rm (x.toRat * pow10 s) <;> simp

/-- `x.divScale y s rm` (`x.divide(y, s, rm)`) rounds `x / y * 10^s` to an integer `r` and
    returns `r × 10^(-s)`. -/
theorem divScale_eq (x y : BigDec) (s : Int) (rm : RoundingMode) (hy : y.unscaled ≠ 0) :
    x.divScale y s rm = (roundRat rm (x.toRat / y.toRat * pow10 s)).map (fun r => ⟨r, s⟩) := by
  have hval : x.toRat / y.toRat * pow10 s =
      (x.unscaled : Rat) / y.unscaled * pow10 (s - x.scale + y.scale) := by
    rw [toRat_def, toRat_def, show s - x.scale + y.scale = s + -x.scale + -(-y.scale) by omega,
      pow10_add, pow10_add, pow10_neg (-y.scale)]
    have := pow10_ne_zero (-y.scale)
    grind
  unfold divScale
  rw [ite_eq_right hy, hval]
  simp only []
  split
  · rename_i he
    rw [divRound_eq _ _ hy, Rat.intCast_mul, pow10Int_cast_toNat he]
    congr 2
    grind
  · rename_i he
    rw [divRound_eq _ _ (Int.mul_ne_zero hy (pow10Int_ne_zero _)), Rat.intCast_mul,
      pow10Int_cast_toNat (by omega), pow10_neg]
    congr 2
    have := pow10_ne_zero (s - x.scale + y.scale)
    grind

theorem divScale_zero {x y : BigDec} {s : Int} {rm : RoundingMode} (hy : y.unscaled = 0) :
    x.divScale y s rm = none := by
  unfold divScale; rw [ite_eq_left hy]

theorem divScale_eq_some {x y z : BigDec} {s : Int} {rm : RoundingMode} :
    x.divScale y s rm = some z ↔
      y.unscaled ≠ 0 ∧ ∃ r, roundRat rm (x.toRat / y.toRat * pow10 s) = some r ∧ z = ⟨r, s⟩ := by
  by_cases hy : y.unscaled = 0
  · simp [divScale_zero hy, hy]
  · rw [divScale_eq x y s rm hy]
    cases roundRat rm (x.toRat / y.toRat * pow10 s) <;> simp [eq_comm, hy]

theorem divScale_toRat {x y z : BigDec} {s r : Int} {rm : RoundingMode}
    (h : x.divScale y s rm = some z) (hr : roundRat rm (x.toRat / y.toRat * pow10 s) = some r) :
    z.toRat = r * pow10 (-s) := by
  obtain ⟨hy, r', hr', rfl⟩ := divScale_eq_some.mp h
  rw [hr] at hr'; cases hr'; rfl

/-! ### Error bounds, in units of the last place `10^(-s)` -/

section bounds

private theorem abs_mul_of_pos (a : Rat) {c : Rat} (hc : 0 < c) : (a * c).abs = a.abs * c := by
  simp only [Rat.abs]
  by_cases ha : 0 ≤ a
  · rw [ite_eq_left ha, ite_eq_left (Rat.mul_nonneg ha (Rat.le_of_lt hc))]
  · have : a * c < 0 := (Rat.mul_neg_iff_of_pos_right hc).mpr (Rat.not_le.mp ha)
    rw [ite_eq_right ha, ite_eq_right (Rat.not_le.mpr this), Rat.neg_mul]

private theorem unscale (v : Rat) (s : Int) : v * pow10 s * pow10 (-s) = v := by
  rw [Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one]

variable {Q : Rat} {r s : Int}

private theorem xfer_abs_le {b : Rat} (h : (Q - r).abs ≤ b) :
    (Q * pow10 (-s) - (⟨r, s⟩ : BigDec).toRat).abs ≤ b * pow10 (-s) := by
  rw [toRat_mk, show Q * pow10 (-s) - r * pow10 (-s) = (Q - r) * pow10 (-s) by grind,
    abs_mul_of_pos _ (pow10_pos _)]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (pow10_pos _))

private theorem xfer_abs_lt {b : Rat} (h : (Q - r).abs < b) :
    (Q * pow10 (-s) - (⟨r, s⟩ : BigDec).toRat).abs < b * pow10 (-s) := by
  rw [toRat_mk, show Q * pow10 (-s) - r * pow10 (-s) = (Q - r) * pow10 (-s) by grind,
    abs_mul_of_pos _ (pow10_pos _)]
  exact Rat.mul_lt_mul_of_pos_right h (pow10_pos _)

private theorem xfer_floor (h : (r : Rat) ≤ Q ∧ Q < r + 1) :
    (⟨r, s⟩ : BigDec).toRat ≤ Q * pow10 (-s) ∧
      Q * pow10 (-s) < (⟨r, s⟩ : BigDec).toRat + pow10 (-s) := by
  rw [toRat_mk]
  have hc := pow10_pos (-s)
  have := Rat.mul_lt_mul_of_pos_right h.2 hc
  exact ⟨Rat.mul_le_mul_of_nonneg_right h.1 (Rat.le_of_lt hc), by grind⟩

private theorem xfer_ceil (h : (r : Rat) - 1 < Q ∧ Q ≤ r) :
    (⟨r, s⟩ : BigDec).toRat - pow10 (-s) < Q * pow10 (-s) ∧
      Q * pow10 (-s) ≤ (⟨r, s⟩ : BigDec).toRat := by
  rw [toRat_mk]
  have hc := pow10_pos (-s)
  have := Rat.mul_lt_mul_of_pos_right h.1 hc
  exact ⟨by grind, Rat.mul_le_mul_of_nonneg_right h.2 (Rat.le_of_lt hc)⟩

private theorem xfer_down (h : (r : Rat).abs ≤ Q.abs ∧ Q.abs - 1 < (r : Rat).abs) :
    (⟨r, s⟩ : BigDec).toRat.abs ≤ (Q * pow10 (-s)).abs ∧
      (Q * pow10 (-s)).abs - pow10 (-s) < (⟨r, s⟩ : BigDec).toRat.abs := by
  rw [toRat_mk, abs_mul_of_pos _ (pow10_pos _), abs_mul_of_pos _ (pow10_pos _)]
  have hc := pow10_pos (-s)
  have := Rat.mul_lt_mul_of_pos_right h.2 hc
  exact ⟨Rat.mul_le_mul_of_nonneg_right h.1 (Rat.le_of_lt hc), by grind⟩

private theorem xfer_up (h : Q.abs ≤ (r : Rat).abs ∧ (r : Rat).abs < Q.abs + 1) :
    (Q * pow10 (-s)).abs ≤ (⟨r, s⟩ : BigDec).toRat.abs ∧
      (⟨r, s⟩ : BigDec).toRat.abs < (Q * pow10 (-s)).abs + pow10 (-s) := by
  rw [toRat_mk, abs_mul_of_pos _ (pow10_pos _), abs_mul_of_pos _ (pow10_pos _)]
  have hc := pow10_pos (-s)
  have := Rat.mul_lt_mul_of_pos_right h.2 hc
  exact ⟨Rat.mul_le_mul_of_nonneg_right h.1 (Rat.le_of_lt hc), by grind⟩

variable {x y z : BigDec}

theorem setScale_HALF_UP_bound (h : x.setScale s .HALF_UP = some z) :
    (x.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_UP_bound hr)
  rw [unscale] at this; grind

theorem setScale_HALF_DOWN_bound (h : x.setScale s .HALF_DOWN = some z) :
    (x.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_DOWN_bound hr)
  rw [unscale] at this; grind

theorem setScale_HALF_EVEN_bound (h : x.setScale s .HALF_EVEN = some z) :
    (x.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_EVEN_bound hr)
  rw [unscale] at this; grind

theorem setScale_FLOOR_bounds (h : x.setScale s .FLOOR = some z) :
    z.toRat ≤ x.toRat ∧ x.toRat < z.toRat + pow10 (-s) := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_floor (s := s) (roundRat_FLOOR_bounds hr)
  rwa [unscale] at this

theorem setScale_CEILING_bounds (h : x.setScale s .CEILING = some z) :
    z.toRat - pow10 (-s) < x.toRat ∧ x.toRat ≤ z.toRat := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_ceil (s := s) (roundRat_CEILING_bounds hr)
  rwa [unscale] at this

theorem setScale_DOWN_bounds (h : x.setScale s .DOWN = some z) :
    z.toRat.abs ≤ x.toRat.abs ∧ x.toRat.abs - pow10 (-s) < z.toRat.abs := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_down (s := s) (roundRat_DOWN_bounds hr)
  rwa [unscale] at this

theorem setScale_UP_bounds (h : x.setScale s .UP = some z) :
    x.toRat.abs ≤ z.toRat.abs ∧ z.toRat.abs < x.toRat.abs + pow10 (-s) := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_up (s := s) (roundRat_UP_bounds hr)
  rwa [unscale] at this

theorem setScale_UNNECESSARY_exact (h : x.setScale s .UNNECESSARY = some z) :
    z.toRat = x.toRat := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  rw [toRat_mk, ← roundRat_UNNECESSARY_exact hr, unscale]

/-- Every mode changes the value by less than one unit in the last place. -/
theorem setScale_bound {rm : RoundingMode} (h : x.setScale s rm = some z) :
    (x.toRat - z.toRat).abs < pow10 (-s) := by
  obtain ⟨r, hr, rfl⟩ := setScale_eq_some.mp h
  have := xfer_abs_lt (s := s) (roundRat_bound hr)
  rw [unscale, Rat.one_mul] at this; exact this

theorem divScale_HALF_UP_bound (h : x.divScale y s .HALF_UP = some z) :
    (x.toRat / y.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_UP_bound hr)
  rw [unscale] at this; grind

theorem divScale_HALF_DOWN_bound (h : x.divScale y s .HALF_DOWN = some z) :
    (x.toRat / y.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_DOWN_bound hr)
  rw [unscale] at this; grind

theorem divScale_HALF_EVEN_bound (h : x.divScale y s .HALF_EVEN = some z) :
    (x.toRat / y.toRat - z.toRat).abs ≤ pow10 (-s) / 2 := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_abs_le (s := s) (roundRat_HALF_EVEN_bound hr)
  rw [unscale] at this; grind

theorem divScale_FLOOR_bounds (h : x.divScale y s .FLOOR = some z) :
    z.toRat ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < z.toRat + pow10 (-s) := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_floor (s := s) (roundRat_FLOOR_bounds hr)
  rwa [unscale] at this

theorem divScale_CEILING_bounds (h : x.divScale y s .CEILING = some z) :
    z.toRat - pow10 (-s) < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ z.toRat := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_ceil (s := s) (roundRat_CEILING_bounds hr)
  rwa [unscale] at this

theorem divScale_DOWN_bounds (h : x.divScale y s .DOWN = some z) :
    z.toRat.abs ≤ (x.toRat / y.toRat).abs ∧
      (x.toRat / y.toRat).abs - pow10 (-s) < z.toRat.abs := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_down (s := s) (roundRat_DOWN_bounds hr)
  rwa [unscale] at this

theorem divScale_UP_bounds (h : x.divScale y s .UP = some z) :
    (x.toRat / y.toRat).abs ≤ z.toRat.abs ∧
      z.toRat.abs < (x.toRat / y.toRat).abs + pow10 (-s) := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_up (s := s) (roundRat_UP_bounds hr)
  rwa [unscale] at this

theorem divScale_UNNECESSARY_exact (h : x.divScale y s .UNNECESSARY = some z) :
    z.toRat = x.toRat / y.toRat := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  rw [toRat_mk, ← roundRat_UNNECESSARY_exact hr, unscale]

theorem divScale_bound {rm : RoundingMode} (h : x.divScale y s rm = some z) :
    (x.toRat / y.toRat - z.toRat).abs < pow10 (-s) := by
  obtain ⟨-, r, hr, rfl⟩ := divScale_eq_some.mp h
  have := xfer_abs_lt (s := s) (roundRat_bound hr)
  rw [unscale, Rat.one_mul] at this; exact this

end bounds

theorem roundRat_DOWN_eq_toBigInt (x : BigDec) : roundRat .DOWN x.toRat = some x.toBigInt := rfl

/-! ## Exact division -/
theorem minScaleOf_strip_spec (n p fuel : Nat) :
    n = (minScaleOf.strip n p fuel).1 * p ^ (minScaleOf.strip n p fuel).2 := by
  induction fuel generalizing n with
  | zero => simp [minScaleOf.strip]
  | succ k ih =>
    simp only [minScaleOf.strip]
    split
    · rename_i h
      have e := ih (n / p)
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← e]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1)).symm
    · simp

/-- `minScaleOf q = some s` makes `q * 10^s` an integer. -/
theorem minScaleOf_spec {q : Rat} {ms : Int} (h : minScaleOf q = some ms) :
    ∃ k : Int, q * pow10 ms = k := by
  have hq : q = (q.num : Rat) / (q.den : Rat) := by rw [← Rat.mkRat_eq_div, Rat.mkRat_self]
  have hden : (q.den : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr q.den_pos)
  unfold minScaleOf at h
  simp only [] at h
  have e1 := minScaleOf_strip_spec q.den 2 (q.den + 1)
  generalize minScaleOf.strip q.den 2 (q.den + 1) = p1 at h e1
  obtain ⟨d1, a⟩ := p1
  have e2 := minScaleOf_strip_spec d1 5 (d1 + 1)
  simp only [] at h e1
  generalize minScaleOf.strip d1 5 (d1 + 1) = p2 at h e2
  obtain ⟨d2, b⟩ := p2
  simp only [] at h e2
  split at h
  · simp at h
  rename_i hd2
  have hd2 : d2 = 1 := by simpa using hd2
  split at h
  · -- an integer: drop its trailing zeros
    rename_i hden1
    have hqn : q = (q.num : Rat) := by
      rw [Rat.eq_iff_mul_eq_mul]; simp [hden1]
    generalize q.num = N at hqn h
    subst hqn
    split at h
    · rename_i hN
      cases h; subst hN
      exact ⟨0, by simp⟩
    · cases h
      have hdvd : ((10 ^ trailingZeros N.natAbs : Nat) : Int) ∣ N :=
        Int.ofNat_dvd_left.mpr (pow10_trailingZeros_dvd _)
      generalize trailingZeros N.natAbs = t at hdvd ⊢
      obtain ⟨k, rfl⟩ := hdvd
      refine ⟨k, ?_⟩
      rw [Rat.intCast_mul, Rat.intCast_natCast, Rat.natCast_pow, Rat.natCast_ofNat,
        ← pow10_natCast]
      have := pow10_mul_pow10_neg (t : Int)
      grind
  · -- denominator `2^a 5^b`: scale `max a b`
    cases h
    have ha : a ≤ a.max b := Nat.le_max_left a b
    have hb : b ≤ a.max b := Nat.le_max_right a b
    generalize a.max b = m at ha hb ⊢
    have hm2 : 2 ^ m = 2 ^ a * 2 ^ (m - a) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hm5 : 5 ^ m = 5 ^ b * 5 ^ (m - b) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hm : 10 ^ m = q.den * (2 ^ (m - a) * 5 ^ (m - b)) := by
      rw [e1, e2, hd2, show (10 : Nat) = 2 * 5 from rfl, Nat.mul_pow, hm2, hm5, Nat.one_mul]
      first | ac_rfl | grind
    refine ⟨q.num * ((2 ^ (m - a) * 5 ^ (m - b) : Nat) : Int), ?_⟩
    have hp : pow10 (m : Int) = (q.den : Rat) * ((2 ^ (m - a) * 5 ^ (m - b) : Nat) : Rat) := by
      rw [pow10_natCast, ← Rat.natCast_ofNat, ← Rat.natCast_pow, hm, Rat.natCast_mul]
    rw [hp, Rat.intCast_mul, Rat.intCast_natCast]
    conv => lhs; rw [hq]
    grind

theorem ofRatAtScale_toRat {q : Rat} {s k : Int} (hk : q * pow10 s = k) :
    (ofRatAtScale q s).toRat = q := by
  simp only [ofRatAtScale, toRat_mk, hk, Rat.floor_intCast]
  rw [← hk, Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one]

theorem mul_pow10_intCast_of_le {q : Rat} {s t k : Int} (hk : q * pow10 s = k) (hst : s ≤ t) :
    q * pow10 t = ((k * pow10Int (t - s).toNat : Int) : Rat) := by
  rw [Rat.intCast_mul, pow10Int_cast_toNat (by omega), ← hk, Rat.mul_assoc, ← pow10_add]
  congr 2; omega

/-- `divide(divisor)` returns the exact quotient. -/
theorem divExact_toRat {x y z : BigDec} (h : x.divExact y = some z) :
    z.toRat = x.toRat / y.toRat := by
  unfold divExact at h
  split at h
  · simp at h
  simp only [] at h
  split at h
  · rename_i hx
    cases h
    simp [toRat_def, hx, Rat.div_def]
  · split at h
    · simp at h
    · rename_i ms hms
      cases h
      obtain ⟨k, hk⟩ := minScaleOf_spec hms
      exact ofRatAtScale_toRat (mul_pow10_intCast_of_le hk (Int.le_max_right _ _))
end BigDec

/-! ## Examples -/

section Examples
open BigDec

-- core `simp` has no `Rat` literal arithmetic; `grind` (or `decide +kernel`) finishes
example : (BigDec.mul ⟨125, 2⟩ ⟨3, 0⟩).toRat = 375/100 := by simp; grind
example : (BigDec.mul ⟨125, 2⟩ ⟨3, 0⟩).toRat = 375/100 := by simp only [jsimp]; grind
example : (BigDec.mul ⟨125, 2⟩ ⟨3, 0⟩).toRat = 375/100 := by decide +kernel

-- `2.345` rounded to two places
example : BigDec.setScale ⟨2345, 3⟩ 2 .HALF_UP = some ⟨235, 2⟩ := by decide
example : BigDec.setScale ⟨2345, 3⟩ 2 .HALF_UP = some ⟨235, 2⟩ := rfl
example : BigDec.setScale ⟨2345, 3⟩ 2 .HALF_EVEN = some ⟨234, 2⟩ := by decide
example : BigDec.setScale ⟨-2345, 3⟩ 2 .HALF_UP = some ⟨-235, 2⟩ := by decide
example : roundRat .HALF_UP ((2345 : Rat) / 1000 * 100) = some 235 := by decide +kernel
example : BigDec.setScale ⟨2345, 3⟩ 2 .UNNECESSARY = none := by decide

-- rounding to cents moves the value by at most half a cent
example (x z : BigDec) (h : x.setScale 2 .HALF_UP = some z) :
    (x.toRat - z.toRat).abs ≤ 1/200 := by
  have := setScale_HALF_UP_bound h
  simp at this
  grind

example (a b c : BigDec) : (a.add b).compareTo c ≤ 0 ↔ a.toRat + b.toRat ≤ c.toRat := by simp

example : BigDec.divExact ⟨1, 0⟩ ⟨8, 0⟩ = some ⟨125, 3⟩ := by decide +kernel

-- the table in the `java.math.RoundingMode` documentation, inputs
-- 5.5, 2.5, 1.6, 1.1, 1.0, -1.0, -1.1, -1.6, -2.5, -5.5
example :
    let xs : List Int := [55, 25, 16, 11, 10, -10, -11, -16, -25, -55]
    let r (rm : RoundingMode) := xs.map fun (n : Int) => roundRat rm ((n : Rat) / 10)
    r .UP = [6, 3, 2, 2, 1, -1, -2, -2, -3, -6].map some ∧
    r .DOWN = [5, 2, 1, 1, 1, -1, -1, -1, -2, -5].map some ∧
    r .CEILING = [6, 3, 2, 2, 1, -1, -1, -1, -2, -5].map some ∧
    r .FLOOR = [5, 2, 1, 1, 1, -1, -2, -2, -3, -6].map some ∧
    r .HALF_UP = [6, 3, 2, 1, 1, -1, -1, -2, -3, -6].map some ∧
    r .HALF_DOWN = [5, 2, 2, 1, 1, -1, -1, -2, -2, -5].map some ∧
    r .HALF_EVEN = [6, 2, 2, 1, 1, -1, -1, -2, -2, -6].map some ∧
    r .UNNECESSARY = [none, none, none, none, some 1, some (-1), none, none, none, none] := by
  decide +kernel

-- the same table through `divRound`, with positive and negative divisors
example :
    let xs : List Int := [55, 25, 16, 11, 10, -10, -11, -16, -25, -55]
    let r (rm : RoundingMode) := xs.map fun n => divRound n 10 rm
    let r' (rm : RoundingMode) := xs.map fun n => divRound (-n) (-10) rm
    r .UP = [6, 3, 2, 2, 1, -1, -2, -2, -3, -6].map some ∧
    r .DOWN = [5, 2, 1, 1, 1, -1, -1, -1, -2, -5].map some ∧
    r .CEILING = [6, 3, 2, 2, 1, -1, -1, -1, -2, -5].map some ∧
    r .FLOOR = [5, 2, 1, 1, 1, -1, -2, -2, -3, -6].map some ∧
    r .HALF_UP = [6, 3, 2, 1, 1, -1, -1, -2, -3, -6].map some ∧
    r .HALF_DOWN = [5, 2, 2, 1, 1, -1, -1, -2, -2, -5].map some ∧
    r .HALF_EVEN = [6, 2, 2, 1, 1, -1, -1, -2, -2, -6].map some ∧
    r .UNNECESSARY = [none, none, none, none, some 1, some (-1), none, none, none, none] ∧
    r' .HALF_EVEN = r .HALF_EVEN ∧ r' .UP = r .UP ∧ r' .FLOOR = r .FLOOR := by
  decide

example (x : BigDec) : x.stripTrailingZeros.compareTo x = 0 := by simp

end Examples

end Jimple
