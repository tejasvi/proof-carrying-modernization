/-
  Jimple/Cobol.lean

  COBOL numeric semantics over `Rat`, for proving that a Java (`BigDecimal`) rewrite of a COBOL
  program computes what the COBOL program computed.

  A numeric item `PIC S9(i)V9(f)` (`Pic`) holds a multiple of `10^(-f)` with at most `i`
  integer digits (`Pic.Fits`). Storing a value into it (IBM Enterprise COBOL, ISO 2002):
  * `MOVE` (`Pic.move`) aligns on the decimal point and drops the excess digits at both ends,
    fraction digits by truncation toward zero;
  * an arithmetic statement (`COMPUTE`, `ADD`, ..., `Pic.compute`) truncates the excess
    fraction digits, or with `ROUNDED` rounds half away from zero, and raises the size error
    condition (`none`) when the result keeps more than `i` integer digits;
    `Pic.computeNoSizeErr` is the value stored when no `ON SIZE ERROR` phrase is coded.
  The stored value is computed from the exact value of the expression; `Pic.compute_align`
  covers compilers that keep only `d > f` fraction digits of it.

  Java counterparts: `setScale(f, DOWN)` and `setScale(f, HALF_UP)` align as COBOL does
  (`BigDec.setScale_rmOf`), so the usual Java idioms (`setScale` or `divide(y, f, mode)`, then
  a range check) store what COBOL stores (`Pic.compute_java`, `Pic.compute_java_range`,
  `Pic.compute_java_divScale`, `Pic.divide_java`), and `remainder(TEN.pow(i))` drops the
  high-order digits as COBOL does (`Pic.computeNoSizeErr_java`, `Pic.move_java`).
-/
import Jimple.DecimalLemmas

namespace Jimple

namespace Cobol

/-- The number of units `10^(-s)` left when `q` is aligned to `s` fraction digits: the excess
    digits are dropped (truncation toward zero), or with `ROUNDED`, 5 is first added to the
    magnitude in the first excess digit (round half away from zero). -/
def units (s : Int) (rounded : Bool) (q : Rat) : Int :=
  let t := q * pow10 s
  ratTrunc (if rounded then (if 0 ≤ t then t + 1/2 else t - 1/2) else t)

/-- `q` aligned to `s` fraction digits, truncated or `ROUNDED`. -/
def align (s : Int) (rounded : Bool) (q : Rat) : Rat := units s rounded q * pow10 (-s)

/-- The Java rounding mode that aligns as COBOL does: `HALF_UP` for `ROUNDED`, else `DOWN`. -/
def rmOf (rounded : Bool) : RoundingMode := if rounded then .HALF_UP else .DOWN

@[simp, jsimp] theorem rmOf_true : rmOf true = .HALF_UP := rfl
@[simp, jsimp] theorem rmOf_false : rmOf false = .DOWN := rfl

/-- Integer facts about `floor` and `ceil`: they are equal or one apart. -/
theorem ceil_eq_floor_or (t : Rat) :
    (t.ceil : Rat) = t.floor ∨ (t.ceil : Rat) = t.floor + 1 := by
  have hf := floor_ceil_facts t
  have h5 : t.ceil ≤ t.floor + 1 := by
    have : (t.ceil : Rat) ≤ ((t.floor + 1 : Int) : Rat) := by push_cast; exact hf.2.2.2.2.1
    exact Rat.intCast_le_intCast.mp this
  have h6 : t.floor ≤ t.ceil := Rat.intCast_le_intCast.mp (Rat.le_trans hf.1 hf.2.2.1)
  rcases (show t.ceil = t.floor ∨ t.ceil = t.floor + 1 by omega) with h | h
  · left; rw [h]
  · right; rw [h]; push_cast; rfl

/-- `HALF_UP` is "add one half to the magnitude, then truncate". -/
theorem roundRat_HALF_UP_eq (t : Rat) :
    roundRat .HALF_UP t = some (ratTrunc (if 0 ≤ t then t + 1/2 else t - 1/2)) := by
  rw [roundRat_HALF_UP]
  congr 1
  have hf := floor_ceil_facts t
  have hcf := ceil_eq_floor_or t
  by_cases ht : 0 ≤ t
  · have h0 : 0 ≤ t + 1/2 := by grind
    simp only [ht, h0, ite_true, ratTrunc]
    split
    · exact (floor_eq_of_le_of_lt (by grind) (by grind)).symm
    · split
      · exact (floor_eq_of_le_of_lt (by grind) (by grind)).symm
      · exact (floor_eq_of_le_of_lt (by grind) (by grind)).symm
  · have h0 : ¬ (0 ≤ t - 1/2) := by grind
    simp only [ht, h0, ite_false, ratTrunc]
    split
    · exact (ceil_eq_of_lt_of_le (by grind) (by grind)).symm
    · split
      · exact (ceil_eq_of_lt_of_le (by grind) (by grind)).symm
      · exact (ceil_eq_of_lt_of_le (by grind) (by grind)).symm

/-- COBOL alignment is `roundRat` with the mode `rmOf`. -/
theorem roundRat_rmOf (s : Int) (rounded : Bool) (q : Rat) :
    roundRat (rmOf rounded) (q * pow10 s) = some (units s rounded q) := by
  cases rounded
  · rfl
  · rw [rmOf_true, roundRat_HALF_UP_eq]; rfl

theorem units_def (s : Int) (rounded : Bool) (q : Rat) : units s rounded q =
    ratTrunc (if rounded then (if 0 ≤ q * pow10 s then q * pow10 s + 1/2 else q * pow10 s - 1/2)
      else q * pow10 s) := rfl

theorem align_def (s : Int) (rounded : Bool) (q : Rat) :
    align s rounded q = units s rounded q * pow10 (-s) := rfl

/-- Aligning a multiple of `10^(-s)` to `s` digits changes nothing. -/
theorem units_of_eq {s : Int} {q : Rat} {n : Int} (h : q * pow10 s = n) (rounded : Bool) :
    units s rounded q = n := by
  rw [units_def, h]
  cases rounded
  · simp [ratTrunc]
  · by_cases hn : (0 : Rat) ≤ n
    · have h0 : (0 : Rat) ≤ n + 1/2 := by grind
      simp only [hn, h0, ite_true, ratTrunc]
      exact floor_eq_of_le_of_lt (by grind) (by grind)
    · have h0 : ¬ ((0 : Rat) ≤ n - 1/2) := by grind
      simp only [hn, h0, ite_false, ite_true, ratTrunc]
      exact ceil_eq_of_lt_of_le (by grind) (by grind)

theorem align_of_eq {s : Int} {q : Rat} {n : Int} (h : q * pow10 s = n) (rounded : Bool) :
    align s rounded q = q := by
  rw [align, units_of_eq h, ← h, Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one]

/-- `|n|` in `Rat` is the cast of `n.natAbs`. -/
theorem abs_intCast (n : Int) : (n : Rat).abs = (n.natAbs : Rat) := by
  by_cases h : 0 ≤ n
  · rw [Rat.abs_of_nonneg (Rat.intCast_nonneg.mpr h), ← Rat.intCast_natCast,
      Int.natAbs_of_nonneg h]
  · rw [Rat.abs_of_nonpos (Rat.intCast_nonpos.mpr (by omega)), ← Rat.intCast_natCast,
      Int.ofNat_natAbs_of_nonpos (by omega), Rat.intCast_neg]

theorem abs_mul_pos (a : Rat) {c : Rat} (hc : 0 < c) : (a * c).abs = a.abs * c := by
  simp only [Rat.abs]
  by_cases ha : 0 ≤ a
  · rw [ite_eq_left ha, ite_eq_left (Rat.mul_nonneg ha (Rat.le_of_lt hc))]
  · have : a * c < 0 := (Rat.mul_neg_iff_of_pos_right hc).mpr (Rat.not_le.mp ha)
    rw [ite_eq_right ha, ite_eq_right (Rat.not_le.mpr this), Rat.neg_mul]

/-- The aligned value in absolute terms: `|units| × 10^(-s)`. -/
theorem abs_align (s : Int) (rounded : Bool) (q : Rat) :
    (align s rounded q).abs = ((units s rounded q).natAbs : Rat) * pow10 (-s) := by
  rw [align, abs_mul_pos _ (pow10_pos _), abs_intCast]

end Cobol

/-! ## Numeric items -/

/-- A numeric COBOL item `PIC S9(i)V9(f)` (`signed`) or `PIC 9(i)V9(f)`: `i` integer digits and
    `f` fraction digits. The `USAGE` (`DISPLAY`, `COMP-3`, `BINARY` with `TRUNC(STD)`) does not
    change the values. -/
structure Pic where
  intDigits : Nat
  fracDigits : Nat
  signed : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Pic
open Cobol

/-- The values the item can hold: multiples of `10^(-f)` below `10^i` in absolute value, and
    not negative when the item is unsigned. -/
def Fits (p : Pic) (q : Rat) : Prop :=
  (∃ n : Int, q * pow10 p.fracDigits = n) ∧ q.abs < pow10 p.intDigits ∧
    (p.signed = false → 0 ≤ q)

/-- `10^(i+f)`: the item holds fewer units `10^(-f)` than this. -/
def capacity (p : Pic) : Nat := 10 ^ (p.intDigits + p.fracDigits)

/-- The value held after storing `n` units `10^(-f)`: only the low `i + f` digits of `n` are
    kept (high-order truncation), and an unsigned item drops the sign. -/
def store (p : Pic) (n : Int) : Rat :=
  let m : Int := (n.natAbs % p.capacity : Nat)
  (if p.signed = true ∧ n < 0 then -m else m) * pow10 (-(p.fracDigits : Int))

/-- `MOVE q TO item` (numeric to numeric): align on the decimal point, drop the excess
    fraction digits (truncation toward zero) and the excess high-order integer digits; an
    unsigned item receives the absolute value. -/
def move (p : Pic) (q : Rat) : Rat := p.store (units p.fracDigits false q)

/-- The result `q` of an arithmetic statement (`COMPUTE`, `ADD`, `SUBTRACT`, `MULTIPLY`,
    `DIVIDE`, with or without `GIVING`) stored into the item. The excess fraction digits are
    truncated, or with `ROUNDED` rounded half away from zero; `none` is the size error
    condition, raised when the aligned result has more than `i` integer digits (with
    `ON SIZE ERROR` the item keeps its old value). An unsigned item stores the absolute value.
    `q` is the exact value of the expression (see `compute_align` for intermediate results
    kept to finitely many digits); division by zero is a size error too (`divide`). -/
def compute (p : Pic) (rounded : Bool) (q : Rat) : Option Rat :=
  let n := units p.fracDigits rounded q
  if n.natAbs < p.capacity then some (p.store n) else none

/-- The value an arithmetic statement without an `ON SIZE ERROR` phrase stores: the excess
    high-order digits are dropped as in `MOVE` (IBM Enterprise COBOL, `DISPLAY` and
    packed-decimal items; the ISO standard leaves this value undefined). -/
def computeNoSizeErr (p : Pic) (rounded : Bool) (q : Rat) : Rat :=
  p.store (units p.fracDigits rounded q)

/-- `DIVIDE b INTO a GIVING item` / `DIVIDE a BY b GIVING item`: dividing by zero is a size
    error. -/
def divide (p : Pic) (rounded : Bool) (a b : Rat) : Option Rat :=
  if b = 0 then none else p.compute rounded (a / b)

-- the automation unfolds the statements to their integer form: unit counts (`units`), the
-- capacity test of the size error, and the kept low-order digits
attribute [jsimp] Pic.compute Pic.computeNoSizeErr Pic.move Pic.store Pic.capacity

theorem capacity_pos (p : Pic) : 0 < p.capacity := Nat.pow_pos (by decide)

theorem capacity_cast (p : Pic) :
    (p.capacity : Rat) = pow10 p.intDigits * pow10 p.fracDigits := by
  rw [capacity, Rat.natCast_pow, Rat.natCast_ofNat, ← pow10_natCast, Int.natCast_add, pow10_add]

theorem store_def (p : Pic) (n : Int) : p.store n =
    ((if p.signed = true ∧ n < 0 then -((n.natAbs % p.capacity : Nat) : Int)
      else ((n.natAbs % p.capacity : Nat) : Int) : Int) : Rat) * pow10 (-(p.fracDigits : Int)) :=
  rfl

theorem store_of_lt {p : Pic} {n : Int} (h : n.natAbs < p.capacity) :
    p.store n = ((if p.signed = true then n else (n.natAbs : Int) : Int) : Rat) *
      pow10 (-(p.fracDigits : Int)) := by
  rw [store_def, Nat.mod_eq_of_lt h]
  congr 2
  by_cases hs : p.signed = true <;> by_cases hn : n < 0 <;> simp [hs, hn] <;> omega

theorem compute_def (p : Pic) (rounded : Bool) (q : Rat) : p.compute rounded q =
    if (units p.fracDigits rounded q).natAbs < p.capacity then
      some (p.store (units p.fracDigits rounded q))
    else none := rfl

/-- `n` units `10^(-f)` fit iff `|n × 10^(-f)| < 10^i`. -/
theorem natAbs_lt_capacity_iff (p : Pic) (n : Int) :
    n.natAbs < p.capacity ↔
      ((n : Rat) * pow10 (-(p.fracDigits : Int))).abs < pow10 p.intDigits := by
  rw [abs_mul_pos _ (pow10_pos _), abs_intCast, ← Rat.natCast_lt_natCast (a := n.natAbs),
    capacity_cast]
  constructor
  · intro h
    have := Rat.mul_lt_mul_of_pos_right h (pow10_pos (-(p.fracDigits : Int)))
    rwa [Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one] at this
  · intro h
    have := Rat.mul_lt_mul_of_pos_right h (pow10_pos (p.fracDigits : Int))
    rwa [Rat.mul_assoc, pow10_neg_mul_pow10, Rat.mul_one] at this

/-- `Fits` in units: `q = n × 10^(-f)` with `|n| < 10^(i+f)`. -/
theorem fits_iff {p : Pic} {q : Rat} : p.Fits q ↔
    ∃ n : Int, q = n * pow10 (-(p.fracDigits : Int)) ∧ n.natAbs < p.capacity ∧
      (p.signed = false → 0 ≤ n) := by
  constructor
  · rintro ⟨⟨n, hn⟩, habs, hsgn⟩
    have hq : q = n * pow10 (-(p.fracDigits : Int)) := by
      rw [← hn, Rat.mul_assoc, pow10_mul_pow10_neg, Rat.mul_one]
    refine ⟨n, hq, (natAbs_lt_capacity_iff p n).mpr (by rw [← hq]; exact habs), fun hs => ?_⟩
    have : (0 : Rat) ≤ n := by
      rw [← hn]; exact Rat.mul_nonneg (hsgn hs) (Rat.le_of_lt (pow10_pos _))
    exact Rat.intCast_nonneg.mp this
  · rintro ⟨n, hq, hlt, hsgn⟩
    refine ⟨⟨n, by rw [hq, Rat.mul_assoc, pow10_neg_mul_pow10, Rat.mul_one]⟩,
      by rw [hq]; exact (natAbs_lt_capacity_iff p n).mp hlt, fun hs => ?_⟩
    rw [hq]; exact Rat.mul_nonneg (Rat.intCast_nonneg.mpr (hsgn hs)) (Rat.le_of_lt (pow10_pos _))

instance (p : Pic) (q : Rat) : Decidable (p.Fits q) :=
  decidable_of_iff (((q * pow10 p.fracDigits).floor : Rat) = q * pow10 p.fracDigits ∧
      q.abs < pow10 p.intDigits ∧ (p.signed = false → 0 ≤ q)) (by
    unfold Fits
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨_, h1.symm⟩, h2, h3⟩
    · rintro ⟨⟨n, hn⟩, h2, h3⟩; exact ⟨by rw [hn, Rat.floor_intCast], h2, h3⟩)

/-- Whatever is stored fits. -/
theorem fits_store (p : Pic) (n : Int) : p.Fits (p.store n) := by
  rw [fits_iff]
  refine ⟨if p.signed = true ∧ n < 0 then -((n.natAbs % p.capacity : Nat) : Int)
    else ((n.natAbs % p.capacity : Nat) : Int), store_def p n, ?_, ?_⟩
  · have := Nat.mod_lt n.natAbs p.capacity_pos
    split <;> simp [Int.natAbs_neg] <;> omega
  · intro hs
    have : ¬ (p.signed = true ∧ n < 0) := by simp [hs]
    rw [ite_eq_right this]; omega

/-- A value that fits is stored unchanged, `ROUNDED` or not. -/
theorem compute_of_fits {p : Pic} {q : Rat} (h : p.Fits q) (rounded : Bool) :
    p.compute rounded q = some q := by
  obtain ⟨n, hq, hlt, hsgn⟩ := fits_iff.mp h
  have hu : units p.fracDigits rounded q = n :=
    units_of_eq (by rw [hq, Rat.mul_assoc, pow10_neg_mul_pow10, Rat.mul_one]) rounded
  rw [compute_def, hu, ite_eq_left hlt, store_of_lt hlt, hq]
  congr 2
  cases hs : p.signed
  · have := hsgn hs; simp; omega
  · rfl

theorem move_def (p : Pic) (q : Rat) : p.move q = p.store (units p.fracDigits false q) := rfl

/-- `MOVE` of a value that fits changes nothing. -/
theorem move_of_fits {p : Pic} {q : Rat} (h : p.Fits q) : p.move q = q := by
  obtain ⟨n, hq, hlt, hsgn⟩ := fits_iff.mp h
  have hu : units p.fracDigits false q = n :=
    units_of_eq (by rw [hq, Rat.mul_assoc, pow10_neg_mul_pow10, Rat.mul_one]) false
  rw [move_def, hu, store_of_lt hlt, hq]
  congr 2
  cases hs : p.signed
  · have := hsgn hs; simp; omega
  · rfl

theorem fits_move (p : Pic) (q : Rat) : p.Fits (p.move q) := fits_store p _

@[simp, jsimp] theorem move_move (p : Pic) (q : Rat) : p.move (p.move q) = p.move q :=
  move_of_fits (fits_move p q)

theorem move_eq_computeNoSizeErr (p : Pic) (q : Rat) : p.move q = p.computeNoSizeErr false q := rfl

theorem fits_computeNoSizeErr (p : Pic) (rounded : Bool) (q : Rat) :
    p.Fits (p.computeNoSizeErr rounded q) := fits_store p _

/-- Without a size error, the stored value is the one without `ON SIZE ERROR`. -/
theorem compute_eq_some {p : Pic} {rounded : Bool} {q v : Rat} (h : p.compute rounded q = some v) :
    v = p.computeNoSizeErr rounded q := by
  rw [compute_def] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

theorem fits_of_compute {p : Pic} {rounded : Bool} {q v : Rat} (h : p.compute rounded q = some v) :
    p.Fits v := by
  rw [compute_eq_some h]; exact fits_computeNoSizeErr p rounded q

/-- The size error condition: the aligned (and rounded) result reaches `10^i`. -/
theorem compute_eq_none_iff {p : Pic} {rounded : Bool} {q : Rat} :
    p.compute rounded q = none ↔ pow10 p.intDigits ≤ (align p.fracDigits rounded q).abs := by
  rw [compute_def, align, ← Rat.not_lt, ← natAbs_lt_capacity_iff]
  split <;> simp_all

theorem compute_isSome_iff {p : Pic} {rounded : Bool} {q : Rat} :
    (p.compute rounded q).isSome ↔ (align p.fracDigits rounded q).abs < pow10 p.intDigits := by
  rw [← Rat.not_le, ← compute_eq_none_iff]
  cases p.compute rounded q <;> simp

/-- Without `ROUNDED` and without a size error, an arithmetic statement stores what `MOVE`
    would. -/
theorem compute_false_eq_move {p : Pic} {q v : Rat} (h : p.compute false q = some v) :
    v = p.move q := compute_eq_some h

/-- A signed item stores the aligned result when it has at most `i` integer digits. -/
theorem compute_signed {p : Pic} (hp : p.signed = true) (rounded : Bool) (q : Rat) :
    p.compute rounded q =
      if (align p.fracDigits rounded q).abs < pow10 p.intDigits then
        some (align p.fracDigits rounded q)
      else none := by
  rw [compute_def, align]
  by_cases h : (units p.fracDigits rounded q).natAbs < p.capacity
  · rw [ite_eq_left h, ite_eq_left ((natAbs_lt_capacity_iff p _).mp h), store_of_lt h]
    simp [hp]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((natAbs_lt_capacity_iff p _).mpr h'))]

/-- An unsigned item stores the absolute value of the aligned result. -/
theorem compute_unsigned {p : Pic} (hp : p.signed = false) (rounded : Bool) (q : Rat) :
    p.compute rounded q =
      if (align p.fracDigits rounded q).abs < pow10 p.intDigits then
        some (align p.fracDigits rounded q).abs
      else none := by
  rw [compute_def, align]
  by_cases h : (units p.fracDigits rounded q).natAbs < p.capacity
  · rw [ite_eq_left h, ite_eq_left ((natAbs_lt_capacity_iff p _).mp h), store_of_lt h,
      abs_mul_pos _ (pow10_pos _), abs_intCast]
    simp [hp, Rat.intCast_natCast]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((natAbs_lt_capacity_iff p _).mpr h'))]

/-- `MOVE` to a signed item without high-order truncation is the aligned value. -/
theorem move_signed {p : Pic} (hp : p.signed = true) {q : Rat}
    (h : (align p.fracDigits false q).abs < pow10 p.intDigits) :
    p.move q = align p.fracDigits false q := by
  have := compute_signed hp false q
  rw [ite_eq_left h] at this
  exact (compute_eq_some this).trans (move_eq_computeNoSizeErr p q).symm |>.symm

@[simp] theorem divide_zero (p : Pic) (rounded : Bool) (a : Rat) : p.divide rounded a 0 = none :=
  rfl

theorem divide_of_ne {p : Pic} {rounded : Bool} {a b : Rat} (hb : b ≠ 0) :
    p.divide rounded a b = p.compute rounded (a / b) := by
  unfold divide; rw [ite_eq_right hb]

end Pic

/-! ## Java (`BigDecimal`) counterparts -/

namespace BigDec
open Cobol

/-- `setScale(s, rmOf rounded)` aligns as COBOL does. -/
theorem setScale_rmOf (x : BigDec) (s : Int) (rounded : Bool) :
    x.setScale s (rmOf rounded) = some ⟨units s rounded x.toRat, s⟩ := by
  rw [setScale_eq, roundRat_rmOf]; rfl

/-- `setScale(s, RoundingMode.DOWN)` truncates as COBOL does. -/
@[jsimp] theorem setScale_DOWN_eq (x : BigDec) (s : Int) :
    x.setScale s .DOWN = some ⟨units s false x.toRat, s⟩ := setScale_rmOf x s false

/-- `setScale(s, RoundingMode.HALF_UP)` rounds as COBOL's `ROUNDED` does. -/
@[jsimp] theorem setScale_HALF_UP_eq (x : BigDec) (s : Int) :
    x.setScale s .HALF_UP = some ⟨units s true x.toRat, s⟩ := setScale_rmOf x s true

theorem setScale_DOWN_map_toRat (x : BigDec) (s : Int) :
    (x.setScale s .DOWN).map toRat = some (align s false x.toRat) := by
  rw [setScale_DOWN_eq]; rfl

theorem setScale_HALF_UP_map_toRat (x : BigDec) (s : Int) :
    (x.setScale s .HALF_UP).map toRat = some (align s true x.toRat) := by
  rw [setScale_HALF_UP_eq]; rfl

/-- `divide(y, s, rmOf rounded)` aligns the exact quotient as COBOL does. -/
theorem divScale_rmOf (x y : BigDec) (s : Int) (rounded : Bool) (hy : y.unscaled ≠ 0) :
    x.divScale y s (rmOf rounded) = some ⟨units s rounded (x.toRat / y.toRat), s⟩ := by
  rw [divScale_eq x y s _ hy, roundRat_rmOf]; rfl

/-- `divide(y, s, RoundingMode.DOWN)` truncates the exact quotient as COBOL does; for a literal
    divisor the side condition is decided, so the failure branch of `divide` disappears. -/
@[jsimp] theorem divScale_DOWN_eq (x y : BigDec) (s : Int) (hy : y.unscaled ≠ 0) :
    x.divScale y s .DOWN = some ⟨units s false (x.toRat / y.toRat), s⟩ :=
  divScale_rmOf x y s false hy

/-- `divide(y, s, RoundingMode.HALF_UP)` rounds the exact quotient as COBOL's `ROUNDED`. -/
@[jsimp] theorem divScale_HALF_UP_eq (x y : BigDec) (s : Int) (hy : y.unscaled ≠ 0) :
    x.divScale y s .HALF_UP = some ⟨units s true (x.toRat / y.toRat), s⟩ :=
  divScale_rmOf x y s true hy

end BigDec

namespace Pic
open Cobol

/-- `10^i` (`BigDecimal.TEN.pow(i)`): the absolute values that fit are below it. -/
def limit (p : Pic) : BigDec := ⟨pow10Int p.intDigits, 0⟩

/-- The largest value the item holds, `9…9.9…9` = `10^i - 10^(-f)`. -/
def maxValue (p : Pic) : BigDec := ⟨p.capacity - 1, p.fracDigits⟩

@[simp, jsimp] theorem toRat_limit (p : Pic) : p.limit.toRat = pow10 p.intDigits := by
  simp [limit]

/-- For a signed item, `compute` is Java's `setScale(f, rmOf rounded)` followed by a size
    check. -/
theorem compute_eq_setScale {p : Pic} (hp : p.signed = true) (rounded : Bool) (x : BigDec) :
    p.compute rounded x.toRat = (x.setScale p.fracDigits (rmOf rounded)).bind
      fun z => if z.toRat.abs < pow10 p.intDigits then some z.toRat else none := by
  rw [BigDec.setScale_rmOf, compute_signed hp]; rfl

/-- The Java idiom for a signed receiving item:
    `z = x.setScale(f, mode); if (z.abs().compareTo(limit) >= 0) → size error; else store z`,
    with `limit = 10^i` (e.g. `p.limit`). -/
theorem compute_java {p : Pic} (hp : p.signed = true) {rounded : Bool} {x z limit : BigDec}
    (hz : x.setScale p.fracDigits (rmOf rounded) = some z) (hl : limit.toRat = pow10 p.intDigits) :
    p.compute rounded x.toRat = if z.abs.compareTo limit < 0 then some z.toRat else none := by
  rw [compute_eq_setScale hp, hz]
  simp [BigDec.toRat_abs, hl]

/-- The same idiom for an unsigned receiving item, which stores `z.abs()`. -/
theorem compute_java_unsigned {p : Pic} (hp : p.signed = false) {rounded : Bool}
    {x z limit : BigDec} (hz : x.setScale p.fracDigits (rmOf rounded) = some z)
    (hl : limit.toRat = pow10 p.intDigits) :
    p.compute rounded x.toRat = if z.abs.compareTo limit < 0 then some z.abs.toRat else none := by
  rw [BigDec.setScale_rmOf] at hz
  cases hz
  rw [compute_unsigned hp]
  have e : (⟨units p.fracDigits rounded x.toRat, p.fracDigits⟩ : BigDec).abs.compareTo limit < 0 ↔
      (align p.fracDigits rounded x.toRat).abs < pow10 p.intDigits := by
    simp [BigDec.toRat_abs, hl, align]
  by_cases h : (align p.fracDigits rounded x.toRat).abs < pow10 p.intDigits
  · rw [ite_eq_left h, ite_eq_left (e.mpr h)]; simp [BigDec.toRat_abs, align]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e.mp h'))]

/-- The range-check idiom: `z.compareTo(MAX) <= 0 && z.compareTo(MAX.negate()) >= 0`, with
    `MAX = 9…9.9…9` (`p.maxValue`). -/
theorem compute_java_range {p : Pic} (hp : p.signed = true) {rounded : Bool} {x z : BigDec}
    (hz : x.setScale p.fracDigits (rmOf rounded) = some z) :
    p.compute rounded x.toRat =
      if z.compareTo p.maxValue ≤ 0 ∧ 0 ≤ z.compareTo p.maxValue.negate then some z.toRat
      else none := by
  rw [BigDec.setScale_rmOf] at hz
  cases hz
  have hc := pow10_pos (-(p.fracDigits : Int))
  have key : ((⟨units p.fracDigits rounded x.toRat, p.fracDigits⟩ : BigDec).compareTo p.maxValue ≤
      0 ∧
      0 ≤ (⟨units p.fracDigits rounded x.toRat, p.fracDigits⟩ : BigDec).compareTo
        p.maxValue.negate) ↔ (units p.fracDigits rounded x.toRat).natAbs < p.capacity := by
    rw [BigDec.compareTo_le_zero_iff, BigDec.compareTo_nonneg_iff, BigDec.toRat_negate]
    simp only [maxValue, BigDec.toRat_mk]
    generalize units p.fracDigits rounded x.toRat = n
    have hcap := p.capacity_pos
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := Rat.le_of_mul_le_mul_right h1 hc
      rw [← Rat.neg_mul] at h2
      have h2' := Rat.le_of_mul_le_mul_right h2 hc
      have a : n ≤ (p.capacity : Int) - 1 := Rat.intCast_le_intCast.mp h1'
      have b : -((p.capacity : Int) - 1) ≤ n := by
        rw [← Rat.intCast_neg] at h2'; exact Rat.intCast_le_intCast.mp h2'
      omega
    · intro h
      have a : n ≤ (p.capacity : Int) - 1 := by omega
      have b : -((p.capacity : Int) - 1) ≤ n := by omega
      constructor
      · exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr a) (Rat.le_of_lt hc)
      · rw [← Rat.neg_mul, ← Rat.intCast_neg]
        exact Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr b) (Rat.le_of_lt hc)
  rw [compute_def]
  by_cases h : (units p.fracDigits rounded x.toRat).natAbs < p.capacity
  · rw [ite_eq_left h, ite_eq_left (key.mpr h), store_of_lt h]; simp [hp]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (key.mp h'))]

/-- Division: `x.divide(y, f, mode)` followed by the size check, for a signed item. -/
theorem compute_java_divScale {p : Pic} (hp : p.signed = true) {rounded : Bool}
    {x y z limit : BigDec} (hz : x.divScale y p.fracDigits (rmOf rounded) = some z)
    (hl : limit.toRat = pow10 p.intDigits) :
    p.compute rounded (x.toRat / y.toRat) =
      if z.abs.compareTo limit < 0 then some z.toRat else none := by
  obtain ⟨hy, -⟩ := BigDec.divScale_eq_some.mp hz
  rw [BigDec.divScale_rmOf x y _ rounded hy] at hz
  cases hz
  rw [compute_signed hp]
  have e : (⟨units p.fracDigits rounded (x.toRat / y.toRat), p.fracDigits⟩ : BigDec).abs.compareTo
      limit < 0 ↔ (align p.fracDigits rounded (x.toRat / y.toRat)).abs < pow10 p.intDigits := by
    simp [BigDec.toRat_abs, hl, align]
  by_cases h : (align p.fracDigits rounded (x.toRat / y.toRat)).abs < pow10 p.intDigits
  · rw [ite_eq_left h, ite_eq_left (e.mpr h)]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e.mp h'))]

/-- `DIVIDE ... GIVING` is Java's `divide(y, f, mode)` with the size check; dividing by zero
    fails on both sides. -/
theorem divide_java {p : Pic} (hp : p.signed = true) (rounded : Bool) (x y : BigDec)
    {limit : BigDec} (hl : limit.toRat = pow10 p.intDigits) :
    p.divide rounded x.toRat y.toRat = (x.divScale y p.fracDigits (rmOf rounded)).bind
      fun z => if z.abs.compareTo limit < 0 then some z.toRat else none := by
  by_cases hy : y.unscaled = 0
  · have : y.toRat = 0 := (BigDec.toRat_eq_zero_iff y).mpr hy
    rw [this, divide_zero, BigDec.divScale_zero hy]; rfl
  · have : y.toRat ≠ 0 := fun h => hy ((BigDec.toRat_eq_zero_iff y).mp h)
    rw [divide_of_ne this, compute_java_divScale hp (BigDec.divScale_rmOf x y _ rounded hy) hl,
      BigDec.divScale_rmOf x y _ rounded hy]
    rfl

end Pic

/-! ## Dropped high-order digits and remainders in Java -/

namespace BigDec

/-- Truncating a quotient of integers is `Int.tdiv`. -/
theorem ratTrunc_intCast_div (n d : Int) (hd : d ≠ 0) : ratTrunc ((n : Rat) / d) = n.tdiv d := by
  have h := divRound_eq n d hd .DOWN
  rw [roundRat_DOWN] at h
  have : divRound n d .DOWN = some (n.tdiv d) := by
    unfold divRound; simp only []; split <;> rfl
  rw [this] at h
  exact (Option.some.inj h).symm

theorem divToIntegral_isSome {x y : BigDec} (hy : y.unscaled ≠ 0) : (x.divToIntegral y).isSome := by
  unfold divToIntegral
  rw [ite_eq_right hy]
  simp only []
  split
  · rfl
  · split <;> rfl

/-- `divideToIntegralValue` is the quotient truncated toward zero. -/
theorem divToIntegral_toRat {x y t : BigDec} (h : x.divToIntegral y = some t) :
    t.toRat = ratTrunc (x.toRat / y.toRat) := by
  unfold divToIntegral at h
  split at h
  · simp at h
  simp only [] at h
  generalize ratTrunc (x.toRat / y.toRat) = T at h ⊢
  split at h
  · rename_i hT; cases h; simp [hT]
  · split at h
    · rename_i hpref; cases h
      rw [toRat_mk, Rat.intCast_mul, pow10Int_cast_toNat hpref, Rat.mul_assoc, pow10_mul_pow10_neg,
        Rat.mul_one]
    · rename_i hpref; cases h
      have hk0 : 0 ≤ Min.min (trailingZeros T.natAbs : Int) (-(x.scale - y.scale)) := by omega
      have hkle : (Min.min (trailingZeros T.natAbs : Int) (-(x.scale - y.scale))).toNat ≤
          trailingZeros T.natAbs := by omega
      have hdvd :
          pow10Int (Min.min (trailingZeros T.natAbs : Int) (-(x.scale - y.scale))).toNat ∣ T := by
        have h1 := Nat.dvd_trans (Nat.pow_dvd_pow 10 hkle) (pow10_trailingZeros_dvd T.natAbs)
        have := Int.ofNat_dvd_left.mpr h1
        simpa [pow10Int, Int.natCast_pow] using this
      generalize Min.min (trailingZeros T.natAbs : Int) (-(x.scale - y.scale)) = k at hk0 hdvd ⊢
      obtain ⟨c, rfl⟩ := hdvd
      rw [toRat_mk, Int.mul_ediv_cancel_left _ (pow10Int_ne_zero _), Int.neg_neg, Rat.intCast_mul,
        pow10Int_cast_toNat hk0, Rat.mul_comm]

/-- `remainder(y)` is `x - trunc(x / y) × y`. -/
theorem remainder_toRat {x y r : BigDec} (h : x.remainder y = some r) :
    r.toRat = x.toRat - ratTrunc (x.toRat / y.toRat) * y.toRat := by
  unfold remainder at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [toRat_sub, toRat_mul, divToIntegral_toRat ht]

/-- `remainder` of decimals in constructor form (`t ≤ s`), as a truncated integer remainder
    at the scale of the dividend; for literal scales and divisor the side conditions are decided. -/
@[jsimp] theorem remainder_mk_of_le {n s v t : Int} (h : t ≤ s) (hv : v ≠ 0) :
    (⟨n, s⟩ : BigDec).remainder ⟨v, t⟩ = some ⟨n.tmod (v * 10 ^ (s - t).toNat), s⟩ := by
  have hP : (10 : Int) ^ (s - t).toNat ≠ 0 := Int.pow_ne_zero (by decide)
  have hV : v * 10 ^ (s - t).toNat ≠ 0 := Int.mul_ne_zero hv hP
  have hcast : (((10 : Int) ^ (s - t).toNat : Int) : Rat) = pow10 (s - t) := by
    have := pow10Int_cast_toNat (show 0 ≤ s - t by omega)
    simpa [pow10Int] using this
  have hT : ratTrunc ((⟨n, s⟩ : BigDec).toRat / (⟨v, t⟩ : BigDec).toRat) =
      n.tdiv (v * 10 ^ (s - t).toNat) := by
    rw [← ratTrunc_intCast_div n _ hV]
    congr 1
    rw [toRat_mk, toRat_mk, Rat.intCast_mul, hcast]
    have e : pow10 (-s) = pow10 (-t) * pow10 (-(s - t)) := by rw [← pow10_add]; congr 1; omega
    have h1 := pow10_ne_zero (-t)
    have h2 := pow10_ne_zero (s - t)
    have h3 : (v : Rat) ≠ 0 := by simpa using hv
    rw [e, pow10_neg (s - t)]
    grind
  unfold remainder divToIntegral
  simp only [hv, ite_false, hT]
  have hpref : 0 ≤ s - t := by omega
  have hs : s - t + t = s := by omega
  by_cases h0 : n.tdiv (v * 10 ^ (s - t).toNat) = 0
  · simp only [h0, ite_true, Option.map_some]
    congr 1
    simp only [sub, add, negate, mul, upscale, BigDec.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Int.tmod_def, h0]; simp [hs, pow10Int]
    · simp [hs]
  · simp only [h0, ite_false, hpref, ite_true, Option.map_some]
    congr 1
    simp only [sub, add, negate, mul, upscale, BigDec.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Int.tmod_def]
      simp only [hs, Int.max_self, Int.sub_self, Int.toNat_zero, pow10Int, Int.pow_zero,
        Int.mul_one]
      simp only [Int.mul_comm, Int.mul_assoc]
      omega
    · simp [hs]

end BigDec

namespace Cobol

/-- The remainder of `DIVIDE ... GIVING q REMAINDER r`: `a - q' × b`, where `q'` is the quotient
    truncated (never rounded, even with `ROUNDED`) to the `s` fraction digits of `q`. It is
    stored into `r` as an arithmetic result is (`Pic.compute pr false`), and only when storing
    the quotient raised no size error. -/
def remainder (s : Int) (a b : Rat) : Rat := a - align s false (a / b) * b

end Cobol

namespace BigDec
open Cobol

/-- The Java remainder idiom `x.subtract(x.divide(y, s, RoundingMode.DOWN).multiply(y))`. -/
theorem sub_divScale_DOWN_mul {x y q : BigDec} {s : Int} (hq : x.divScale y s .DOWN = some q) :
    (x.sub (q.mul y)).toRat = Cobol.remainder s x.toRat y.toRat := by
  obtain ⟨hy, -⟩ := divScale_eq_some.mp hq
  rw [show RoundingMode.DOWN = rmOf false from rfl, divScale_rmOf x y s false hy] at hq
  cases hq
  rw [toRat_sub, toRat_mul, Cobol.remainder]; rfl

/-- `x.remainder(y)` is the `DIVIDE` remainder for a quotient without fraction digits. -/
theorem remainder_eq_cobol {x y r : BigDec} (h : x.remainder y = some r) :
    r.toRat = Cobol.remainder 0 x.toRat y.toRat := by
  rw [remainder_toRat h, Cobol.remainder, align, units_def]
  simp

end BigDec

namespace Pic
open Cobol

/-- A signed item keeps `n.tmod 10^(i+f)` units: `Int.tmod` keeps the sign of `n`. -/
theorem store_signed {p : Pic} (hp : p.signed = true) (n : Int) :
    p.store n = (n.tmod p.capacity : Rat) * pow10 (-(p.fracDigits : Int)) := by
  rw [store_def]
  congr 2
  have h1 := Int.natAbs_tmod n p.capacity
  have h2 : 0 ≤ n → 0 ≤ n.tmod p.capacity := Int.tmod_nonneg _
  have h3 : n ≤ 0 → n.tmod p.capacity ≤ 0 := fun h => by
    have := Int.tmod_nonneg (p.capacity : Int) (show 0 ≤ -n by omega)
    rw [Int.neg_tmod] at this; omega
  simp only [hp, true_and, Int.natAbs_natCast] at h1 ⊢
  generalize n.natAbs % p.capacity = m at h1 ⊢
  split <;> omega

/-- Without `ON SIZE ERROR`, a signed item drops the high-order digits as Java's
    `z.remainder(BigDecimal.TEN.pow(i))` does, for `z = x.setScale(f, mode)`. -/
theorem computeNoSizeErr_java {p : Pic} (hp : p.signed = true) {rounded : Bool}
    {x z limit : BigDec} (hz : x.setScale p.fracDigits (rmOf rounded) = some z)
    (hl : limit.toRat = pow10 p.intDigits) :
    (z.remainder limit).map BigDec.toRat = some (p.computeNoSizeErr rounded x.toRat) := by
  rw [BigDec.setScale_rmOf] at hz
  cases hz
  have hlu : limit.unscaled ≠ 0 := fun h => by
    have := (BigDec.toRat_eq_zero_iff limit).mpr h
    rw [hl] at this; exact pow10_ne_zero _ this
  have hsome :
      (BigDec.remainder ⟨units p.fracDigits rounded x.toRat, p.fracDigits⟩ limit).isSome := by
    unfold BigDec.remainder
    have :=
      BigDec.divToIntegral_isSome (x := ⟨units p.fracDigits rounded x.toRat, p.fracDigits⟩) hlu
    revert this; cases BigDec.divToIntegral _ limit <;> simp
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  rw [BigDec.remainder_toRat hr, hl, computeNoSizeErr, store_signed hp, BigDec.toRat_mk]
  generalize units p.fracDigits rounded x.toRat = n
  have hcap : (p.capacity : Int) ≠ 0 := by have := p.capacity_pos; omega
  have hpf := pow10_mul_pow10_neg (p.fracDigits : Int)
  have hi := pow10_ne_zero (p.intDigits : Int)
  have hf := pow10_ne_zero (p.fracDigits : Int)
  have hc : ((p.capacity : Int) : Rat) = pow10 p.intDigits * pow10 p.fracDigits := by
    rw [Rat.intCast_natCast, capacity_cast]
  have hdiv : (n : Rat) * pow10 (-(p.fracDigits : Int)) / pow10 p.intDigits =
      (n : Rat) / ((p.capacity : Int) : Rat) := by
    rw [hc]; grind
  rw [hdiv, BigDec.ratTrunc_intCast_div n _ hcap]
  have key : ((n.tmod p.capacity : Int) : Rat) +
      ((p.capacity : Int) : Rat) * (n.tdiv p.capacity : Int) = n := by
    rw [← Rat.intCast_mul, ← Rat.intCast_add, Int.tmod_add_mul_tdiv]
  rw [hc] at key
  grind

/-- `MOVE` to a signed item in Java: `x.setScale(f, RoundingMode.DOWN).remainder(TEN.pow(i))`. -/
theorem move_java {p : Pic} (hp : p.signed = true) {x z limit : BigDec}
    (hz : x.setScale p.fracDigits .DOWN = some z) (hl : limit.toRat = pow10 p.intDigits) :
    (z.remainder limit).map BigDec.toRat = some (p.move x.toRat) :=
  computeNoSizeErr_java hp (rounded := false) hz hl

end Pic

/-! ## Intermediate results -/

namespace Cobol

theorem ratTrunc_of_nonneg {x : Rat} (h : 0 ≤ x) : ratTrunc x = x.floor := by
  rw [ratTrunc, ite_eq_left h]

theorem ratTrunc_of_nonpos {x : Rat} (h : x ≤ 0) : ratTrunc x = x.ceil := by
  unfold ratTrunc
  split
  · rename_i h'
    have : x = 0 := Rat.le_antisymm h h'
    subst this; rfl
  · rfl

private theorem le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [← Rat.not_lt, Rat.div_lt_iff hc, Rat.not_lt]

private theorem div_le_iff {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  rw [← Rat.not_lt, Rat.lt_div_iff hc, Rat.not_lt]

private theorem div_le_div {a b c : Rat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_iff hc, Rat.div_mul_cancel (Rat.ne_of_gt hc)]; exact h

/-- Truncating to an integer first does not change the truncated quotient by `K > 0`. -/
theorem ratTrunc_trunc_div (t : Rat) {K : Int} (hK : 0 < K) :
    ratTrunc ((ratTrunc t : Rat) / K) = ratTrunc (t / K) := by
  have hKR : (0 : Rat) < K := Rat.intCast_pos.mpr hK
  have hf := floor_ceil_facts t
  by_cases ht : 0 ≤ t
  · rw [ratTrunc_of_nonneg ht]
    have hT : (0 : Rat) ≤ t.floor := hf.2.2.2.2.2.1 ht
    have h1 : 0 ≤ (t.floor : Rat) / K := by
      rw [le_div_iff hKR, Rat.zero_mul]; exact hT
    have h2 : 0 ≤ t / K := by rw [le_div_iff hKR, Rat.zero_mul]; exact ht
    rw [ratTrunc_of_nonneg h1, ratTrunc_of_nonneg h2]
    have hz := floor_ceil_facts (t / K)
    apply floor_eq_of_le_of_lt
    · rw [le_div_iff hKR]
      have a : ((t / K).floor : Rat) * K ≤ t := (le_div_iff hKR).mp hz.1
      have b : (t / K).floor * K ≤ t.floor := Rat.le_floor_iff.mpr (by push_cast; exact a)
      have := Rat.intCast_le_intCast.mpr b
      push_cast at this; exact this
    · have := div_le_div hKR hf.1
      grind
  · have ht' : t ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ht)
    rw [ratTrunc_of_nonpos ht']
    have hT : (t.ceil : Rat) ≤ 0 := hf.2.2.2.2.2.2 ht'
    have h1 : (t.ceil : Rat) / K ≤ 0 := by
      rw [div_le_iff hKR, Rat.zero_mul]; exact hT
    have h2 : t / K ≤ 0 := by rw [div_le_iff hKR, Rat.zero_mul]; exact ht'
    rw [ratTrunc_of_nonpos h1, ratTrunc_of_nonpos h2]
    have hz := floor_ceil_facts (t / K)
    apply ceil_eq_of_lt_of_le
    · have := div_le_div hKR hf.2.2.1
      grind
    · rw [div_le_iff hKR]
      have a : t ≤ ((t / K).ceil : Rat) * K := (div_le_iff hKR).mp hz.2.2.1
      have b : t.ceil ≤ (t / K).ceil * K := Rat.ceil_le_iff.mpr (by push_cast; exact a)
      have := Rat.intCast_le_intCast.mpr b
      push_cast at this; exact this

/-- Rounding half away from zero is not changed by first truncating to the grid `1/K`, `K`
    even: the halfway points lie on that grid. -/
theorem halfUp_trunc_div (t : Rat) {K : Int} (hK : 2 ≤ K) (hK2 : K % 2 = 0) :
    ratTrunc (if 0 ≤ (ratTrunc (t * K) : Rat) / K then (ratTrunc (t * K) : Rat) / K + 1/2
      else (ratTrunc (t * K) : Rat) / K - 1/2) =
    ratTrunc (if 0 ≤ t then t + 1/2 else t - 1/2) := by
  obtain ⟨M, hM⟩ : ∃ M : Int, K = 2 * M := ⟨K / 2, by omega⟩
  have hKR : (0 : Rat) < K := Rat.intCast_pos.mpr (by omega)
  have hKM : (K : Rat) = 2 * M := by rw [hM]; push_cast; rfl
  have hftk := floor_ceil_facts (t * K)
  by_cases ht : 0 ≤ t
  · have htk : 0 ≤ t * K := Rat.mul_nonneg ht (Rat.le_of_lt hKR)
    rw [ratTrunc_of_nonneg htk]
    have hT : (0 : Rat) ≤ (t * K).floor := hftk.2.2.2.2.2.1 htk
    have hx : 0 ≤ ((t * K).floor : Rat) / K := by rw [le_div_iff hKR, Rat.zero_mul]; exact hT
    simp only [hx, ht, ite_true]
    rw [ratTrunc_of_nonneg (by grind), ratTrunc_of_nonneg (by grind)]
    have ha := floor_ceil_facts (t + 1/2)
    have hTt : ((t * K).floor : Rat) / K ≤ t := by
      have := div_le_div hKR hftk.1
      rwa [Rat.mul_div_cancel (Rat.ne_of_gt hKR)] at this
    generalize (t + 1/2).floor = a at ha ⊢
    apply floor_eq_of_le_of_lt
    · have h1 : ((a : Rat) - 1/2) * K ≤ t * K :=
        Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hKR)
      have h2 : ((a * K - M : Int) : Rat) ≤ t * K := by
        push_cast; rw [hKM] at h1 ⊢; grind
      have h3 := Rat.intCast_le_intCast.mpr (Rat.le_floor_iff.mpr h2)
      have h5 : (a : Rat) - 1/2 ≤ ((t * K).floor : Rat) / K := by
        rw [le_div_iff hKR]; push_cast at h3; rw [hKM] at h3 ⊢; grind
      grind
    · grind
  · have ht' : t < 0 := Rat.not_le.mp ht
    have htk : t * K ≤ 0 := Rat.le_of_lt ((Rat.mul_neg_iff_of_pos_right hKR).mpr ht')
    rw [ratTrunc_of_nonpos htk]
    have hT : ((t * K).ceil : Rat) ≤ 0 := hftk.2.2.2.2.2.2 htk
    simp only [ht, ite_false]
    rw [ratTrunc_of_nonpos (show t - 1/2 ≤ 0 by grind)]
    have hb := floor_ceil_facts (t - 1/2)
    by_cases hT0 : ((t * K).ceil : Rat) = 0
    · have hgt : -1 < t * K := by grind
      have hK2R : (2 : Rat) ≤ K := by exact_mod_cast hK
      have hkk : (0 : Rat) ≤ (-t) * ((K : Rat) - 2) := Rat.mul_nonneg (by grind) (by grind)
      rw [hT0, Rat.div_def, Rat.zero_mul]
      have e1 : ratTrunc (if (0 : Rat) ≤ 0 then 0 + 1/2 else 0 - 1/2) = 0 := by decide +kernel
      rw [e1]
      exact (ceil_eq_of_lt_of_le (by push_cast; grind) (by push_cast; grind)).symm
    · have hTneg : ((t * K).ceil : Rat) < 0 := Rat.lt_of_le_of_ne hT hT0
      have hx : ¬ (0 ≤ ((t * K).ceil : Rat) / K) := by
        rw [Rat.not_le, Rat.div_lt_iff hKR, Rat.zero_mul]; exact hTneg
      simp only [hx, ite_false]
      have htT : t ≤ ((t * K).ceil : Rat) / K := by
        have := div_le_div hKR hftk.2.2.1
        rwa [Rat.mul_div_cancel (Rat.ne_of_gt hKR)] at this
      rw [ratTrunc_of_nonpos (by grind)]
      generalize (t - 1/2).ceil = b at hb ⊢
      apply ceil_eq_of_lt_of_le
      · grind
      · have h1 : t * K ≤ ((b : Rat) + 1/2) * K :=
          Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hKR)
        have h2 : t * K ≤ ((b * K + M : Int) : Rat) := by
          push_cast; rw [hKM] at h1 ⊢; grind
        have h4 := Rat.intCast_le_intCast.mpr (Rat.ceil_le_iff.mpr h2)
        have h5 : ((t * K).ceil : Rat) / K ≤ (b : Rat) + 1/2 := by
          rw [div_le_iff hKR]; push_cast at h4; rw [hKM] at h4 ⊢; grind
        grind

private theorem pow10Int_even {m : Nat} (hm : 1 ≤ m) : 2 ≤ pow10Int m ∧ pow10Int m % 2 = 0 := by
  have h : pow10Int m = 2 * (5 * pow10Int (m - 1)) := by
    unfold pow10Int
    rw [show m = (m - 1) + 1 by omega, Int.pow_succ]
    simp only [Nat.add_sub_cancel]
    rw [Int.mul_comm, ← Int.mul_assoc]; rfl
  have := pow10Int_pos (m - 1)
  omega

/-- Truncating first to `d ≥ s` digits does not change truncation to `s` digits. -/
theorem units_align_false {s d : Int} (h : s ≤ d) (q : Rat) :
    units s false (align d false q) = units s false q := by
  have hK : 0 < pow10Int (d - s).toNat := pow10Int_pos _
  have hc : ((pow10Int (d - s).toNat : Int) : Rat) = pow10 (d - s) := pow10Int_cast_toNat (by omega)
  have hd : pow10 d = pow10 s * pow10 (d - s) := by rw [← pow10_add]; congr 1; omega
  have hsd : pow10 (d - s) ≠ 0 := pow10_ne_zero _
  have hdd := pow10_mul_pow10_neg d
  have e1 : (ratTrunc (q * pow10 d) : Rat) * pow10 (-d) * pow10 s =
      (ratTrunc (q * pow10 d) : Rat) / ((pow10Int (d - s).toNat : Int) : Rat) := by
    rw [hc]; rw [hd] at hdd; grind
  have e2 : q * pow10 s = q * pow10 d / ((pow10Int (d - s).toNat : Int) : Rat) := by
    rw [hc, hd]; grind
  rw [units_def, units_def, align, units_def]
  simp only [Bool.false_eq_true, ite_false]
  rw [e1, e2]
  exact ratTrunc_trunc_div _ hK

/-- Truncating first to `d > s` digits does not change rounding half away from zero to `s`
    digits. -/
theorem units_align_true {s d : Int} (h : s < d) (q : Rat) :
    units s true (align d false q) = units s true q := by
  have hK := pow10Int_even (m := (d - s).toNat) (by omega)
  have hc : ((pow10Int (d - s).toNat : Int) : Rat) = pow10 (d - s) := pow10Int_cast_toNat (by omega)
  have hd : pow10 d = pow10 s * pow10 (d - s) := by rw [← pow10_add]; congr 1; omega
  have hsd : pow10 (d - s) ≠ 0 := pow10_ne_zero _
  have hdd := pow10_mul_pow10_neg d
  have e1 : (ratTrunc (q * pow10 d) : Rat) * pow10 (-d) * pow10 s =
      (ratTrunc (q * pow10 d) : Rat) / ((pow10Int (d - s).toNat : Int) : Rat) := by
    rw [hc]; rw [hd] at hdd; grind
  have e2 : q * pow10 d = q * pow10 s * ((pow10Int (d - s).toNat : Int) : Rat) := by
    rw [hc, hd, Rat.mul_assoc]
  rw [units_def, units_def, align, units_def]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [e1, e2]
  exact halfUp_trunc_div _ hK.1 hK.2

end Cobol

namespace Pic
open Cobol

/-- Intermediate results: a compiler that keeps only `d > f` fraction digits of the exact
    result, dropping the rest, stores what the exact result gives. -/
theorem compute_align {p : Pic} {d : Int} (hd : (p.fracDigits : Int) < d) (rounded : Bool)
    (q : Rat) : p.compute rounded (align d false q) = p.compute rounded q := by
  have hu : units p.fracDigits rounded (align d false q) = units p.fracDigits rounded q := by
    cases rounded
    · exact units_align_false (Int.le_of_lt hd) q
    · exact units_align_true hd q
  rw [compute_def, compute_def, hu]

theorem computeNoSizeErr_align {p : Pic} {d : Int} (hd : (p.fracDigits : Int) < d)
    (rounded : Bool) (q : Rat) :
    p.computeNoSizeErr rounded (align d false q) = p.computeNoSizeErr rounded q := by
  have hu : units p.fracDigits rounded (align d false q) = units p.fracDigits rounded q := by
    cases rounded
    · exact units_align_false (Int.le_of_lt hd) q
    · exact units_align_true hd q
  rw [computeNoSizeErr, computeNoSizeErr, hu]

theorem move_align {p : Pic} {d : Int} (hd : (p.fracDigits : Int) ≤ d) (q : Rat) :
    p.move (align d false q) = p.move q := by
  rw [move_def, move_def, units_align_false hd]

end Pic

/-! ## Example: monthly interest

```
       05 BAL   PIC S9(7)V99.
       05 RATE  PIC 9(2)V9(4).
       05 INT   PIC S9(5)V99.
           COMPUTE INT ROUNDED = BAL * RATE / 1200
```
rewritten in Java as
`bal.multiply(rate).divide(BigDecimal.valueOf(1200), 2, RoundingMode.HALF_UP)`.
-/

namespace CobolExample
open Cobol

def balPic : Pic := ⟨7, 2, true⟩
def ratePic : Pic := ⟨2, 4, false⟩
def intPic : Pic := ⟨5, 2, true⟩

/-- `COMPUTE INT ROUNDED = BAL * RATE / 1200` -/
def interestCobol (bal rate : Rat) : Option Rat := intPic.compute true (bal * rate / 1200)

/-- `bal.multiply(rate).divide(BigDecimal.valueOf(1200), 2, RoundingMode.HALF_UP)` -/
def interestJava (bal rate : BigDec) : Option BigDec :=
  (bal.mul rate).divScale ⟨1200, 0⟩ 2 .HALF_UP

-- 12345.67 at 5.25 %: 54.01230625 is stored as 54.01
example : balPic.Fits (1234567/100) ∧ ratePic.Fits (525/100) := by decide +kernel
example : interestCobol (1234567/100) (525/100) = some (5401/100) := by decide +kernel
example : interestJava ⟨1234567, 2⟩ ⟨52500, 4⟩ = some ⟨5401, 2⟩ := by decide
-- ties round away from zero: 30.00 at 0.2 % is 0.005
example : interestCobol 30 (2/10) = some (1/100) := by decide +kernel
example : interestCobol (-30) (2/10) = some (-1/100) := by decide +kernel
example : interestJava ⟨-3000, 2⟩ ⟨2000, 4⟩ = some ⟨-1, 2⟩ := by decide
-- without ROUNDED the excess digits are dropped
example : intPic.compute false ((-30) * (2/10) / 1200) = some 0 := by decide +kernel
-- size error: 9999999.99 at 99.9999 % is 833332.4991…, rounded 833332.50: six integer digits
example : interestCobol (999999999/100) (999999/10000) = none := by decide +kernel
-- ... and without ON SIZE ERROR the high-order digit is lost: 33332.50
example : intPic.computeNoSizeErr true (999999999/100 * (999999/10000) / 1200) = 3333250/100 := by
  decide +kernel

/-- The Java rewrite computes `COMPUTE INT ROUNDED = BAL * RATE / 1200`, size error included:
    Java checks `z.abs().compareTo(BigDecimal.TEN.pow(5)) < 0`. -/
theorem interest_java_eq_cobol {bal rate z : BigDec} (hz : interestJava bal rate = some z) :
    interestCobol bal.toRat rate.toRat =
      if z.abs.compareTo intPic.limit < 0 then some z.toRat else none := by
  have := Pic.compute_java_divScale (p := intPic) rfl (rounded := true) (x := bal.mul rate)
    (y := ⟨1200, 0⟩) hz (Pic.toRat_limit _)
  unfold interestCobol
  rw [← this]
  congr 1
  simp

/-- Without a size error the Java result is the COBOL result. -/
theorem interest_java_eq_cobol_of_lt {bal rate z : BigDec} (hz : interestJava bal rate = some z)
    (hsize : z.toRat.abs < 100000) : interestCobol bal.toRat rate.toRat = some z.toRat := by
  rw [interest_java_eq_cobol hz, ite_eq_left]
  have h5 : pow10 (intPic.intDigits : Int) = 100000 := by decide +kernel
  rw [BigDec.compareTo_lt_zero_iff, BigDec.toRat_abs, Pic.toRat_limit, h5]
  exact hsize

/-- The Java computation never throws: the divisor is not zero. -/
theorem interestJava_isSome (bal rate : BigDec) : (interestJava bal rate).isSome := by
  unfold interestJava
  rw [BigDec.divScale_eq _ _ _ _ (by decide)]
  have := roundRat_isSome (rm := .HALF_UP) (by decide)
    ((bal.mul rate).toRat / (⟨1200, 0⟩ : BigDec).toRat * pow10 2)
  revert this
  cases roundRat .HALF_UP ((bal.mul rate).toRat / (⟨1200, 0⟩ : BigDec).toRat * pow10 2) <;> simp

end CobolExample

end Jimple
