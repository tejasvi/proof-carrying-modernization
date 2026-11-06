/-
# Java target model

Exact models of the Java numeric types a COBOL rewrite uses, built on the same scaled-integer
and rounding primitives as the COBOL semantics, so that equivalence proofs are mostly
definitional:

* `Java.BigDecimal` (`java.math.BigDecimal`): unscaled `Int` + scale, exact `add`,
  `subtract`, `multiply`, `setScale`, `divide(divisor, scale, mode)`, `compareTo`,
  `movePointLeft/Right`, `round(MathContext)`, `longValue` ...  Operations that throw
  `ArithmeticException` return `Except`.
* `int` / `long` are Lean's `Int32` / `Int64` (two's-complement wrapping, exactly Java's
  semantics); `Java.Math.*Exact` throw on overflow.
* `Java.RoundingMode.*` are the COBOL rounding modes under their Java names.

A Java method is transcribed into a Lean function over these types (one Lean `def` per
method, `Except` for exceptions, `List`/fold for loops over collections).
-/
import Cobol.Sem.Arith
import Cobol.Logic.Attr

namespace Java
open Cobol

/-- `java.lang.ArithmeticException` causes. -/
inductive ArithmeticException where
  | divideByZero
  | roundingNecessary
  | overflow
  deriving DecidableEq, Repr, Inhabited

/-! `java.math.RoundingMode` (the COBOL modes under their Java names). -/
namespace RoundingMode
abbrev UP : Cobol.RoundingMode := .awayFromZero
abbrev DOWN : Cobol.RoundingMode := .truncation
abbrev CEILING : Cobol.RoundingMode := .towardGreater
abbrev FLOOR : Cobol.RoundingMode := .towardLesser
abbrev HALF_UP : Cobol.RoundingMode := .nearestAwayFromZero
abbrev HALF_DOWN : Cobol.RoundingMode := .nearestTowardZero
abbrev HALF_EVEN : Cobol.RoundingMode := .nearestEven
abbrev UNNECESSARY : Cobol.RoundingMode := .prohibited
end RoundingMode

/-- `java.math.BigDecimal`: the value `unscaled * 10^(-scale)`. -/
structure BigDecimal where
  unscaled : Int
  scale : Int
  deriving DecidableEq, Repr, Inhabited

namespace BigDecimal

/-- `BigDecimal.valueOf(unscaledVal, scale)`. -/
def valueOf (v : Int) (scale : Int := 0) : BigDecimal := ⟨v, scale⟩

def ZERO : BigDecimal := ⟨0, 0⟩
def ONE : BigDecimal := ⟨1, 0⟩

/-- `this.add(b)`: exact, scale `max`. -/
def add (a b : BigDecimal) : BigDecimal :=
  let s := max a.scale b.scale
  ⟨Sem.align a.unscaled a.scale s + Sem.align b.unscaled b.scale s, s⟩

/-- `this.subtract(b)`. -/
def subtract (a b : BigDecimal) : BigDecimal :=
  let s := max a.scale b.scale
  ⟨Sem.align a.unscaled a.scale s - Sem.align b.unscaled b.scale s, s⟩

/-- `this.multiply(b)`: exact, scale `a.scale + b.scale`. -/
def multiply (a b : BigDecimal) : BigDecimal := ⟨a.unscaled * b.unscaled, a.scale + b.scale⟩

def negate (a : BigDecimal) : BigDecimal := ⟨-a.unscaled, a.scale⟩

def abs (a : BigDecimal) : BigDecimal := ⟨(a.unscaled.natAbs : Int), a.scale⟩

/-- `this.signum()`. -/
def signum (a : BigDecimal) : Int := if a.unscaled < 0 then -1 else if a.unscaled = 0 then 0 else 1

/-- `this.compareTo(b)`: numeric comparison (scale-insensitive), `-1` / `0` / `1`. -/
def compareTo (a b : BigDecimal) : Int :=
  let s := max a.scale b.scale
  let x := Sem.align a.unscaled a.scale s
  let y := Sem.align b.unscaled b.scale s
  if x < y then -1 else if x = y then 0 else 1

/-- `this.equals(b)`: scale-sensitive (`2.0` is not equal to `2.00`). -/
def equals (a b : BigDecimal) : Bool := a.unscaled == b.unscaled && a.scale == b.scale

/-- `this.setScale(newScale, mode)`. -/
def setScale (a : BigDecimal) (s : Int) (m : Cobol.RoundingMode) :
    Except ArithmeticException BigDecimal :=
  if m == .prohibited && !Sem.rescaleExact a.unscaled a.scale s then
    throw .roundingNecessary
  else pure ⟨rescale m a.unscaled a.scale s, s⟩

/-- `this.divide(divisor, scale, mode)`. -/
def divide (a b : BigDecimal) (s : Int) (m : Cobol.RoundingMode) :
    Except ArithmeticException BigDecimal :=
  if b.unscaled = 0 then throw .divideByZero
  else if m == .prohibited && !Sem.quotExact a.unscaled a.scale b.unscaled b.scale s then
    throw .roundingNecessary
  else pure ⟨Sem.quot m a.unscaled a.scale b.unscaled b.scale s, s⟩

/-- `this.divide(divisor, mode)`: result scale is `this.scale()`. -/
def divideRM (a b : BigDecimal) (m : Cobol.RoundingMode) : Except ArithmeticException BigDecimal :=
  divide a b a.scale m

/-- `this.divideToIntegralValue(divisor)` (truncated quotient, scale `a.scale - b.scale` when
non-negative; this model returns scale 0). -/
def divideToIntegralValue (a b : BigDecimal) : Except ArithmeticException BigDecimal :=
  if b.unscaled = 0 then throw .divideByZero
  else pure ⟨Sem.quot .truncation a.unscaled a.scale b.unscaled b.scale 0, 0⟩

/-- `this.remainder(divisor)`: `this - this.divideToIntegralValue(divisor) * divisor`. -/
def remainder (a b : BigDecimal) : Except ArithmeticException BigDecimal := do
  let q ← divideToIntegralValue a b
  pure (subtract a (multiply q b))

/-- `this.movePointLeft(n)`: scale `max(scale + n, 0)`. -/
def movePointLeft (a : BigDecimal) (n : Int) : BigDecimal :=
  let s := a.scale + n
  if 0 ≤ s then ⟨a.unscaled, s⟩ else ⟨a.unscaled * 10 ^ (-s).toNat, 0⟩

/-- `this.movePointRight(n)`. -/
def movePointRight (a : BigDecimal) (n : Int) : BigDecimal := movePointLeft a (-n)

/-- `this.scaleByPowerOfTen(n)`. -/
def scaleByPowerOfTen (a : BigDecimal) (n : Int) : BigDecimal := ⟨a.unscaled, a.scale - n⟩

/-- `this.precision()`: number of digits of the unscaled value (1 for zero). -/
def precision (a : BigDecimal) : Nat := Sem.numDigits a.unscaled.natAbs

/-- `this.round(new MathContext(p, mode))` for `p > 0`. -/
def round (a : BigDecimal) (p : Nat) (m : Cobol.RoundingMode) :
    Except ArithmeticException BigDecimal :=
  let pr := a.precision
  if p = 0 ∨ pr ≤ p then pure a
  else
    let drop := pr - p
    if m == .prohibited && a.unscaled % (10 ^ drop : Int) != 0 then throw .roundingNecessary
    else
      let q := divRound m a.unscaled (10 ^ drop)
      -- a carry (e.g. 999 -> 1000) adds a digit: drop one more (exact)
      if Sem.numDigits q.natAbs > p then pure ⟨q / 10, a.scale - drop - 1⟩
      else pure ⟨q, a.scale - drop⟩

/-- `this.toBigInteger()`: truncation toward zero. -/
def toBigInteger (a : BigDecimal) : Int := rescale .truncation a.unscaled a.scale 0

/-- `this.longValue()`: truncation, then the low-order 64 bits. -/
def longValue (a : BigDecimal) : Int64 := Int64.ofInt a.toBigInteger

/-- `this.intValue()`: truncation, then the low-order 32 bits. -/
def intValue (a : BigDecimal) : Int32 := Int32.ofInt a.toBigInteger

/-- `this.longValueExact()`. -/
def longValueExact (a : BigDecimal) : Except ArithmeticException Int64 :=
  if !Sem.rescaleExact a.unscaled a.scale 0 then throw .roundingNecessary
  else
    let v := a.toBigInteger
    if -(2 ^ 63 : Int) ≤ v ∧ v < 2 ^ 63 then pure (Int64.ofInt v) else throw .overflow

/-- Numeric value as a scaled integer at scale `s` (exact when `s ≥ scale`). -/
def valueAt (a : BigDecimal) (s : Int) : Int := rescale .truncation a.unscaled a.scale s

instance : Add BigDecimal := ⟨add⟩
instance : Sub BigDecimal := ⟨subtract⟩
instance : Mul BigDecimal := ⟨multiply⟩
instance : Neg BigDecimal := ⟨negate⟩

end BigDecimal

/-! `java.lang.Math` exact integer arithmetic. -/
namespace Math

def addExact (a b : Int64) : Except ArithmeticException Int64 :=
  let r := a.toInt + b.toInt
  if -(2 ^ 63 : Int) ≤ r ∧ r < 2 ^ 63 then pure (a + b) else throw .overflow

def subtractExact (a b : Int64) : Except ArithmeticException Int64 :=
  let r := a.toInt - b.toInt
  if -(2 ^ 63 : Int) ≤ r ∧ r < 2 ^ 63 then pure (a - b) else throw .overflow

def multiplyExact (a b : Int64) : Except ArithmeticException Int64 :=
  let r := a.toInt * b.toInt
  if -(2 ^ 63 : Int) ≤ r ∧ r < 2 ^ 63 then pure (a * b) else throw .overflow

/-- `Math.floorDiv` for `long`. -/
def floorDiv (a b : Int64) : Except ArithmeticException Int64 :=
  if b = 0 then throw .divideByZero else pure (Int64.ofInt (divRoundZ .towardLesser a.toInt b.toInt))

/-- `Math.floorMod` for `long`. -/
def floorMod (a b : Int64) : Except ArithmeticException Int64 :=
  if b = 0 then throw .divideByZero
  else pure (Int64.ofInt (a.toInt - b.toInt * divRoundZ .towardLesser a.toInt b.toInt))

end Math

/-- A Java `int` holding a small value. -/
theorem int32_toInt_ofInt {x : Int} (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) :
    (Int32.ofInt x).toInt = x := Int32.toInt_ofInt_of_le h1 h2

theorem int32_ofInt_eq_zero {x : Int} (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) :
    (Int32.ofInt x = 0) ↔ x = 0 := by
  rw [← Int32.toInt_inj, int32_toInt_ofInt h1 h2]
  simp

/-- `int` / `long` equality is equality of the values. -/
theorem int32_eq_iff (a b : Int32) : (a = b) = (a.toInt = b.toInt) := propext Int32.toInt_inj.symm
theorem int64_eq_iff (a b : Int64) : (a = b) = (a.toInt = b.toInt) := propext Int64.toInt_inj.symm

/-- Java `long` division `a / b` (truncation; `Long.MIN_VALUE / -1` wraps). -/
def ldiv (a b : Int64) : Except ArithmeticException Int64 :=
  if b = 0 then throw .divideByZero else pure (a / b)

/-- Java `long` remainder `a % b` (sign of the dividend). -/
def lrem (a b : Int64) : Except ArithmeticException Int64 :=
  if b = 0 then throw .divideByZero else pure (a % b)

attribute [java_eval] BigDecimal.valueOf BigDecimal.ZERO BigDecimal.ONE BigDecimal.add
  BigDecimal.subtract BigDecimal.multiply BigDecimal.negate BigDecimal.abs BigDecimal.signum
  BigDecimal.compareTo BigDecimal.equals BigDecimal.setScale BigDecimal.divide BigDecimal.divideRM
  BigDecimal.divideToIntegralValue BigDecimal.remainder BigDecimal.movePointLeft
  BigDecimal.movePointRight BigDecimal.scaleByPowerOfTen BigDecimal.toBigInteger
  BigDecimal.longValue BigDecimal.intValue BigDecimal.longValueExact BigDecimal.valueAt
  Math.addExact Math.subtractExact Math.multiplyExact Math.floorDiv Math.floorMod ldiv lrem
  int32_eq_iff int64_eq_iff Int32.toInt_zero Int64.toInt_zero

end Java
