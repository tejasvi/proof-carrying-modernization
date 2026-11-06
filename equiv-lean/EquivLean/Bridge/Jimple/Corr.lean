import EquivLean.Repr.Int
import EquivLean.Repr.Decimal
import EquivLean.Repr.Corr
import Jimple

/-!
# JimpleLean values and the shared models

* Java `int`/`long` (`Value.int`/`Value.long`, `BitVec 32/64`) represent mathematical integers
  through `SRepr` (`EquivLean.Repr.Int`): `IntVal v i`, `LongVal v i`.
* `java.math.BigDecimal` (JimpleLean's `BigDec`: unscaled `Int`, scale `Int`) is the shared
  `Decimal` (`EquivLean.Repr.Decimal`) with the same fields (`ofBigDec`), and the same value
  (`val_ofBigDec`: `toRat` is `Decimal.val`).  The operations agree: `add`, `mul`, `negate`
  (by definition), `setScale`/`divide(divisor, scale, mode)` (`setScale_toRM`, `divScale_toRM`:
  JimpleLean's `roundRat` and the shared `Decimal.roundRat` have the same arms), and COBOL-style
  alignment `Cobol.units` (`units_eq_roundRat`, `units_eq_divRound`), which is how a JimpleLean
  proof of a COBOL rewrite meets coblean's integer `Cobol.divRound`.
* `Corr BigDec Decimal` relates equal values (scale-insensitive, as `compareTo`).
-/

open Jimple

namespace EquivLean.Jimple

/-! ## Integers -/

/-- `v` is a Java `int` holding the integer `i`. -/
def IntVal (v : Value) (i : Int) : Prop := ∃ x : I32, v = .int x ∧ SRepr x i

/-- `v` is a Java `long` holding the integer `i`. -/
def LongVal (v : Value) (i : Int) : Prop := ∃ x : I64, v = .long x ∧ SRepr x i

theorem intVal_int (x : I32) : IntVal (.int x) x.toInt := ⟨x, rfl, rfl⟩
theorem longVal_long (x : I64) : LongVal (.long x) x.toInt := ⟨x, rfl, rfl⟩

theorem intVal_iff {v : Value} {i : Int} : IntVal v i ↔ ∃ x : I32, v = .int x ∧ x.toInt = i :=
  Iff.rfl

/-! ## Rounding modes -/

/-- The JimpleLean rounding mode of a shared rounding mode (`UNNECESSARY` has no counterpart:
it is "exact or throw"). -/
def toRM : EquivLean.RoundingMode → Jimple.RoundingMode
  | .UP => .UP
  | .DOWN => .DOWN
  | .CEILING => .CEILING
  | .FLOOR => .FLOOR
  | .HALF_UP => .HALF_UP
  | .HALF_DOWN => .HALF_DOWN
  | .HALF_EVEN => .HALF_EVEN

/-- The two rounding specifications agree arm by arm. -/
theorem roundRat_toRM (m : EquivLean.RoundingMode) (q : Rat) :
    Jimple.roundRat (toRM m) q = some (Decimal.roundRat m q) := by
  cases m <;> rfl

/-- JimpleLean's `divRound` (with `tdiv`/`tmod`) is the shared one for a positive divisor. -/
theorem divRound_toRM (m : EquivLean.RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    Jimple.divRound n d (toRM m) = some (Decimal.divRound m n d) := by
  rw [Jimple.divRound_eq n d (by omega), roundRat_toRM, Decimal.divRound_eq_roundRat m n hd]

/-! ## Decimals -/

/-- A JimpleLean `BigDec` as a shared decimal (same unscaled value and scale). -/
def ofBigDec (d : BigDec) : Decimal := ⟨d.unscaled, d.scale⟩

/-- A shared decimal as a JimpleLean `BigDec`. -/
def toBigDec (d : Decimal) : BigDec := ⟨d.unscaled, d.scale⟩

@[simp] theorem toBigDec_ofBigDec (d : BigDec) : toBigDec (ofBigDec d) = d := rfl
@[simp] theorem ofBigDec_toBigDec (d : Decimal) : ofBigDec (toBigDec d) = d := rfl

/-- `BigDec.toRat` is `Decimal.val`. -/
theorem val_ofBigDec (d : BigDec) : (ofBigDec d).val = d.toRat := by
  simp only [ofBigDec, Decimal.val, BigDec.toRat, pow10_eq_zpow]

/-- Value correspondence: a `BigDecimal` and a shared decimal with the same value. -/
instance instCorrBigDecDecimal : Corr BigDec Decimal := ⟨fun b d => b.toRat = d.val⟩

theorem corr_ofBigDec (d : BigDec) : Corr.corr d (ofBigDec d) := (val_ofBigDec d).symm

theorem ofBigDec_add (x y : BigDec) : ofBigDec (x.add y) = (ofBigDec x).add (ofBigDec y) := rfl
theorem ofBigDec_mul (x y : BigDec) : ofBigDec (x.mul y) = (ofBigDec x).mul (ofBigDec y) := rfl
theorem ofBigDec_negate (x : BigDec) : ofBigDec x.negate = (ofBigDec x).neg := rfl

/-- `setScale(s, mode)` is the shared `rescale`. -/
theorem setScale_toRM (x : BigDec) (s : Int) (m : EquivLean.RoundingMode) :
    x.setScale s (toRM m) = some (toBigDec ((ofBigDec x).rescale s m)) := by
  rw [BigDec.setScale_eq, roundRat_toRM]
  simp only [Option.map_some, toBigDec, Decimal.rescale, Decimal.rescaleInt_eq_roundRat,
    val_ofBigDec, pow10_eq_zpow]

/-- `divide(divisor, s, mode)` is the shared `div`. -/
theorem divScale_toRM (x y : BigDec) (s : Int) (m : EquivLean.RoundingMode)
    (hy : y.unscaled ≠ 0) :
    x.divScale y s (toRM m) = ((ofBigDec x).div (ofBigDec y) s m).map toBigDec := by
  rw [BigDec.divScale_eq x y s _ hy, roundRat_toRM,
    Decimal.div_eq_roundRat _ _ s m (by simpa [ofBigDec] using hy)]
  simp only [Option.map_some, toBigDec, val_ofBigDec, pow10_eq_zpow]

/-! ## COBOL alignment (`Cobol.units`) and coblean's integer rounding -/

/-- JimpleLean's COBOL alignment with `ROUNDED` is the shared half-up rounding. -/
theorem units_eq_roundRat (s : Int) (q : Rat) :
    Jimple.Cobol.units s true q = Decimal.roundRat .HALF_UP (q * pow10 s) := by
  have h := Jimple.Cobol.roundRat_rmOf s true q
  rw [Jimple.Cobol.rmOf_true, show Jimple.RoundingMode.HALF_UP = toRM .HALF_UP from rfl,
    roundRat_toRM] at h
  exact (Option.some.inj h).symm

/-- **Alignment of an exact quotient.**  When `q · 10^s = n / D` (`D > 0`), COBOL-style rounding
of `q` to `s` places is the integer half-up division of `n` by `D`: the shared
`Decimal.divRound .HALF_UP`, which is coblean's `Cobol.divRound .nearestAwayFromZero`
(`EquivLean.Cobol.divRound_cobol`). -/
theorem units_eq_divRound {s : Int} {q : Rat} {n D : Int} (hD : 0 < D)
    (h : q * pow10 s = (n : Rat) / D) :
    Jimple.Cobol.units s true q = Decimal.divRound .HALF_UP n D := by
  rw [units_eq_roundRat, h, Decimal.divRound_eq_roundRat _ _ hD]

end EquivLean.Jimple
