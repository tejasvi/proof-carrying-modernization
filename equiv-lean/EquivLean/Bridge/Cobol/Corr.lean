import EquivLean.Repr.Corr
import EquivLean.Repr.Decimal
import Cobol

/-!
# coblean values and the shared `Decimal` model

coblean represents every fixed-point quantity as a scaled integer, and so does
`EquivLean.Decimal`; this file states the correspondences, all of them definitional or one
case split:

* **PIC fields**: a numeric item with format `f` holding bytes `bs` stands for the decimal
  `⟨v, f.scale⟩` where `decodeNum c f bs = some v` (`fieldDec`, `PicCorr`); a stored value
  `encodeNum c f v` decodes back when it fits (`fieldDec_encodeNum`).
* **Rounding**: `Cobol.RoundingMode` (COBOL 2014 names, plus `PROHIBITED`) ↦
  `EquivLean.RoundingMode` (`ofCobol`, `toCobol`); `Cobol.divRound`, `divRoundZ`, `rescale`,
  `Sem.align`, `Sem.quot` are `Decimal.divRound`, `divRoundZ`, `rescaleInt`, `align`,
  `quotInt` (`divRound_cobol`, …).
* **Java** (coblean's `Java.BigDecimal` model): `ofBig` is a bijection onto `Decimal` that
  commutes with `add`, `subtract`, `multiply`, `negate`, `setScale`, `divide`, `compareTo`.
* **Rust**: `i64` / `i128` scaled integers (`scaled s v := ⟨v, s⟩`, `cents`), the
  hand-written half-up division idiom (`divRound_halfUp_idiom_dec`), and the exact subset of
  `rust_decimal::Decimal` (`ofRustDec`).

`Corr` instances: `Java.BigDecimal`/`Decimal` and `Rust.Decimal`/`Decimal` by `ofBig b = d`
(scale-sensitive, as `BigDecimal.equals`).
-/

open Cobol

namespace EquivLean.Cobol

open EquivLean (Decimal RoundingMode)

/-! ## PIC fields -/

/-- The decimal a numeric item holds: its decoded scaled integer at the item's scale
(`none` for invalid data). -/
def fieldDec (c : Config) (f : NumFmt) (bs : List UInt8) : Option Decimal :=
  (decodeNum c f bs).map fun v => ⟨v, f.scale⟩

/-- `bs` (the bytes of an item with format `f`) represents the decimal `d`. -/
def PicCorr (c : Config) (f : NumFmt) (bs : List UInt8) (d : Decimal) : Prop :=
  fieldDec c f bs = some d

theorem fieldDec_of_decode {c : Config} {f : NumFmt} {bs : List UInt8} {v : Int}
    (h : decodeNum c f bs = some v) : fieldDec c f bs = some ⟨v, f.scale⟩ := by
  simp [fieldDec, h]

theorem picCorr_iff {c : Config} {f : NumFmt} {bs : List UInt8} {d : Decimal} :
    PicCorr c f bs d ↔ decodeNum c f bs = some d.unscaled ∧ d.scale = f.scale := by
  unfold PicCorr fieldDec
  cases h : decodeNum c f bs with
  | none => simp
  | some v =>
    obtain ⟨u, s⟩ := d
    simp only [Option.map_some, Option.some.injEq, Decimal.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- A stored value that fits the item decodes to itself: storing a decimal at the item's
scale and reading it back is the identity. -/
theorem fieldDec_encodeNum (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits)
    (hd18 : f.digits ≤ 18) (h : f.Holds c v) :
    fieldDec c f (encodeNum c f v) = some ⟨v, f.scale⟩ :=
  fieldDec_of_decode (decodeNum_encodeNum c f v hd hd18 h)

/-- The value of a field as a rational number. -/
theorem fieldDec_val {c : Config} {f : NumFmt} {bs : List UInt8} {v : Int}
    (h : decodeNum c f bs = some v) :
    (fieldDec c f bs).map Decimal.val = some ((v : Rat) * (10 : Rat) ^ (-f.scale)) := by
  simp [fieldDec, h, Decimal.val]

/-! ## Rounding modes -/

/-- COBOL `ROUNDED MODE` ↦ shared rounding mode.  `PROHIBITED` rounds like `TRUNCATION`
(coblean's `divRound` truncates and reports inexactness separately, `Cobol.Exact`). -/
def ofCobol : Cobol.RoundingMode → RoundingMode
  | .awayFromZero => .UP
  | .nearestAwayFromZero => .HALF_UP
  | .nearestEven => .HALF_EVEN
  | .nearestTowardZero => .HALF_DOWN
  | .towardGreater => .CEILING
  | .towardLesser => .FLOOR
  | .truncation => .DOWN
  | .prohibited => .DOWN

/-- Shared rounding mode ↦ COBOL `ROUNDED MODE`. -/
def toCobol : RoundingMode → Cobol.RoundingMode
  | .UP => .awayFromZero
  | .DOWN => .truncation
  | .CEILING => .towardGreater
  | .FLOOR => .towardLesser
  | .HALF_UP => .nearestAwayFromZero
  | .HALF_DOWN => .nearestTowardZero
  | .HALF_EVEN => .nearestEven

@[simp] theorem ofCobol_toCobol (m : RoundingMode) : ofCobol (toCobol m) = m := by
  cases m <;> rfl

theorem toCobol_ofCobol (m : Cobol.RoundingMode) (h : m ≠ .prohibited) :
    toCobol (ofCobol m) = m := by
  cases m <;> first | rfl | exact absurd rfl h

/-- coblean's rounding primitive is the shared one (the arms are literally the same). -/
theorem divRound_cobol (m : Cobol.RoundingMode) (n d : Int) :
    Cobol.divRound m n d = Decimal.divRound (ofCobol m) n d := by
  cases m <;> rfl

theorem divRound_toCobol (m : RoundingMode) (n d : Int) :
    Cobol.divRound (toCobol m) n d = Decimal.divRound m n d := by
  cases m <;> rfl

theorem divRoundZ_cobol (m : Cobol.RoundingMode) (n d : Int) :
    Cobol.divRoundZ m n d = Decimal.divRoundZ (ofCobol m) n d := by
  simp only [Cobol.divRoundZ, Decimal.divRoundZ, divRound_cobol]

/-- `Cobol.rescale m v s t` is the unscaled value of `⟨v, s⟩` rescaled to `t`. -/
theorem rescale_cobol (m : Cobol.RoundingMode) (v s t : Int) :
    Cobol.rescale m v s t = (Decimal.mk v s).rescaleInt t (ofCobol m) := by
  simp only [Cobol.rescale, Decimal.rescaleInt, Decimal.align, divRound_cobol]

theorem rescale_toCobol (m : RoundingMode) (x : Decimal) (t : Int) :
    Cobol.rescale (toCobol m) x.unscaled x.scale t = x.rescaleInt t m := by
  rw [rescale_cobol, ofCobol_toCobol]

/-- `Sem.align` (exact upscaling) is `Decimal.align`. -/
theorem align_cobol (v s t : Int) : Sem.align v s t = (Decimal.mk v s).align t := rfl

/-- `Sem.quot` (the quotient of COBOL division and of `BigDecimal.divide`) is
`Decimal.quotInt`. -/
theorem quot_cobol (m : Cobol.RoundingMode) (x sx y sy t : Int) :
    Sem.quot m x sx y sy t = (Decimal.mk x sx).quotInt ⟨y, sy⟩ t (ofCobol m) := by
  simp only [Sem.quot, Decimal.quotInt, divRoundZ_cobol]

/-- `Sem.rescaleExact` is `Decimal.ExactAt`. -/
theorem rescaleExact_iff (v s t : Int) :
    Sem.rescaleExact v s t = true ↔ (Decimal.mk v s).ExactAt t := by
  simp only [Sem.rescaleExact, Decimal.ExactAt, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro (h | h) ht
    · omega
    · exact h
  · intro h
    by_cases hst : s ≤ t
    · exact .inl hst
    · exact .inr (h (by omega))

/-! ## Java (`Java.BigDecimal`) -/

/-- A `BigDecimal` as a decimal (the same unscaled value and scale). -/
def ofBig (b : Java.BigDecimal) : Decimal := ⟨b.unscaled, b.scale⟩

/-- A decimal as a `BigDecimal`. -/
def toBig (d : Decimal) : Java.BigDecimal := ⟨d.unscaled, d.scale⟩

@[simp] theorem ofBig_toBig (d : Decimal) : ofBig (toBig d) = d := rfl
@[simp] theorem toBig_ofBig (b : Java.BigDecimal) : toBig (ofBig b) = b := rfl

theorem ofBig_inj {a b : Java.BigDecimal} : ofBig a = ofBig b ↔ a = b :=
  ⟨fun h => by rw [← toBig_ofBig a, h, toBig_ofBig], fun h => h ▸ rfl⟩

@[simp] theorem ofBig_valueOf (v s : Int) : ofBig (Java.BigDecimal.valueOf v s) = ⟨v, s⟩ := rfl

@[simp] theorem ofBig_add (a b : Java.BigDecimal) : ofBig (a.add b) = (ofBig a).add (ofBig b) :=
  rfl

@[simp] theorem ofBig_subtract (a b : Java.BigDecimal) :
    ofBig (a.subtract b) = (ofBig a).sub (ofBig b) := rfl

@[simp] theorem ofBig_multiply (a b : Java.BigDecimal) :
    ofBig (a.multiply b) = (ofBig a).mul (ofBig b) := rfl

@[simp] theorem ofBig_negate (a : Java.BigDecimal) : ofBig a.negate = (ofBig a).neg := rfl

/-- `setScale(s, m)` with a real rounding mode is `Decimal.rescale`. -/
theorem setScale_eq (a : Java.BigDecimal) (s : Int) (m : RoundingMode) :
    a.setScale s (toCobol m) = .ok (toBig ((ofBig a).rescale s m)) := by
  have : (toCobol m == Cobol.RoundingMode.prohibited) = false := by cases m <;> rfl
  simp only [Java.BigDecimal.setScale, this, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [rescale_cobol, ofCobol_toCobol]
  rfl

/-- `setScale(s, UNNECESSARY)`: the decimal itself (at scale `s`) when it is exact there. -/
theorem setScale_unnecessary (a : Java.BigDecimal) (s : Int) (h : (ofBig a).ExactAt s) :
    ofBig <$> a.setScale s .prohibited = .ok ((ofBig a).rescale s .DOWN) := by
  have he : Sem.rescaleExact a.unscaled a.scale s = true := (rescaleExact_iff _ _ _).2 h
  simp only [Java.BigDecimal.setScale, he, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [rescale_cobol]
  rfl

/-- `divide(b, s, m)` with a real rounding mode is `Decimal.div` (`ArithmeticException` for a
zero divisor). -/
theorem divide_eq (a b : Java.BigDecimal) (s : Int) (m : RoundingMode) :
    a.divide b s (toCobol m) =
      match (ofBig a).div (ofBig b) s m with
      | some d => .ok (toBig d)
      | none => .error .divideByZero := by
  have : (toCobol m == Cobol.RoundingMode.prohibited) = false := by cases m <;> rfl
  unfold Java.BigDecimal.divide Decimal.div
  by_cases hb : b.unscaled = 0
  · simp only [hb, ↓reduceIte, ofBig]; rfl
  · simp only [hb, ↓reduceIte, this, Bool.false_and, Bool.false_eq_true, ofBig]
    rw [quot_cobol, ofCobol_toCobol]
    rfl

/-- `compareTo` is `Decimal.cmp`: `-1`, `0`, `1` for `<`, `=`, `>` of the values. -/
theorem compareTo_eq (a b : Java.BigDecimal) :
    a.compareTo b = match (ofBig a).cmp (ofBig b) with
      | .lt => -1 | .eq => 0 | .gt => 1 := by
  have key : ∀ x y : Int, (if x < y then (-1 : Int) else if x = y then 0 else 1) =
      match compare x y with | .lt => -1 | .eq => 0 | .gt => 1 := by
    intro x y
    by_cases h1 : x < y
    · simp [h1, Int.compare_eq_lt.2 h1]
    · by_cases h2 : x = y
      · simp [h2]
      · have h3 : y < x := by omega
        simp [h1, h2, Int.compare_eq_gt.2 h3]
  exact key _ _

theorem compareTo_lt_iff (a b : Java.BigDecimal) :
    a.compareTo b = -1 ↔ (ofBig a).val < (ofBig b).val := by
  rw [compareTo_eq, ← Decimal.cmp_eq_lt_iff]
  cases (ofBig a).cmp (ofBig b) <;> simp

theorem compareTo_eq_zero_iff (a b : Java.BigDecimal) :
    a.compareTo b = 0 ↔ (ofBig a).val = (ofBig b).val := by
  rw [compareTo_eq, ← Decimal.cmp_eq_eq_iff]
  cases (ofBig a).cmp (ofBig b) <;> simp

/-- `valueAt s` (the value as a scaled integer at scale `s`) is a truncating rescale. -/
theorem valueAt_eq (a : Java.BigDecimal) (s : Int) :
    a.valueAt s = (ofBig a).rescaleInt s .DOWN := by
  simp only [Java.BigDecimal.valueAt, rescale_cobol]
  rfl

instance : Corr Java.BigDecimal Decimal := ⟨fun b d => ofBig b = d⟩

@[simp] theorem corr_big_iff (b : Java.BigDecimal) (d : Decimal) :
    Corr.corr b d ↔ ofBig b = d := Iff.rfl

/-! ## Rust scaled integers -/

/-- A scaled integer of a Rust rewrite (`i64` cents, `i128` intermediates) at scale `s`. -/
def scaled (s : Int) (v : Int) : Decimal := ⟨v, s⟩

/-- `i64` cents. -/
def cents (x : Int64) : Decimal := scaled 2 x.toInt

@[simp] theorem scaled_val (s v : Int) : (scaled s v).val = (v : Rat) * (10 : Rat) ^ (-s) := rfl

/-- The hand-written Rust "divide, rounding half away from zero" idiom
`if n >= 0 { (2*n + d) / (2*d) } else { -((2*-n + d) / (2*d)) }` (`d > 0`, Rust `/` on
non-negative operands) is `Decimal.divRound .HALF_UP`. -/
theorem divRound_halfUp_idiom_dec (n d : Int) :
    (if 0 ≤ n then (2 * n + d) / (2 * d) else -((2 * -n + d) / (2 * d))) =
      Decimal.divRound .HALF_UP n d := rfl

/-- The same through coblean's transcription (`Rust.div128` = truncating division). -/
theorem divRound_halfUp_idiom_rust (n d : Int) (hd : 0 < d) :
    (if 0 ≤ n then Cobol.divRound .truncation (2 * n + d) (2 * d)
      else -Cobol.divRound .truncation (2 * -n + d) (2 * d)) = Decimal.divRound .HALF_UP n d := by
  rw [Rust.divRound_halfUp_idiom n d (2 * d) hd rfl, divRound_cobol]; rfl

/-- Rescaling a scaled integer with the Rust idiom: `(v * 10^k)` up, `div_half_up(v, 10^k)`
down. -/
theorem rescale_scaled_halfUp (v : Int) (s t : Int) (h : t < s) :
    ((scaled s v).rescale t .HALF_UP).unscaled =
      Decimal.divRound .HALF_UP v (10 ^ (s - t).toNat) := by
  rw [Decimal.rescale_unscaled, Decimal.rescaleInt_of_lt (scaled s v) .HALF_UP h]; rfl

/-- `rust_decimal::Decimal` (exact subset) as a decimal. -/
def ofRustDec (d : Rust.Decimal) : Decimal := ⟨d.mantissa, d.scale⟩

theorem ofRustDec_checkedAdd {a b c : Rust.Decimal} (h : a.checkedAdd b = some c) :
    ofRustDec c = (ofRustDec a).add (ofRustDec b) := by
  unfold Rust.Decimal.checkedAdd Rust.Decimal.new at h
  dsimp only at h
  split at h
  · cases h
    have hm : ((max a.scale b.scale : Nat) : Int) = max (a.scale : Int) (b.scale : Int) := by
      omega
    simp only [ofRustDec, Decimal.add, Decimal.common, Decimal.align, Sem.align, hm]
  · cases h

theorem ofRustDec_checkedMul {a b c : Rust.Decimal} (h : a.checkedMul b = some c) :
    ofRustDec c = (ofRustDec a).mul (ofRustDec b) := by
  unfold Rust.Decimal.checkedMul Rust.Decimal.new at h
  split at h
  · cases h; simp [ofRustDec, Decimal.mul]
  · cases h

/-- `round_dp_with_strategy(dp, m)` rounds to `dp` places (or keeps a smaller scale). -/
theorem ofRustDec_roundDp (a : Rust.Decimal) (dp : Nat) (m : RoundingMode)
    (h : dp < a.scale) :
    ofRustDec (a.roundDp dp (toCobol m)) = (ofRustDec a).rescale dp m := by
  simp only [Rust.Decimal.roundDp, h, ↓reduceIte, ofRustDec, Decimal.rescale,
    Decimal.rescaleInt, divRound_toCobol]
  have h' : ¬ ((a.scale : Int) ≤ (dp : Int)) := by omega
  simp only [h', ↓reduceIte, Decimal.mk.injEq, and_true]
  congr 2
  omega

instance : Corr Rust.Decimal Decimal := ⟨fun r d => ofRustDec r = d⟩

end EquivLean.Cobol
