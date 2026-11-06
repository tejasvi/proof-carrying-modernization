/-
  Jimple/Decimal.lean

  `java.math.BigDecimal` as an exact decimal: an unscaled integer and a scale,
  denoting `unscaled × 10^(-scale)`. Every operation follows the JDK specification,
  including result scales (which `equals`, `toString` and `hashCode` can observe).
  `BigDec.toRat` maps a value into `Rat`, so specifications and proofs can be stated
  with ordinary rational arithmetic (`Jimple/DecimalLemmas.lean`).

  Operations that throw `ArithmeticException` in Java return `none`.
-/
import Jimple.JString

namespace Jimple

/-- `java.math.RoundingMode`, in declaration order (= ordinal = legacy `ROUND_*` int). -/
inductive RoundingMode where
  | UP | DOWN | CEILING | FLOOR | HALF_UP | HALF_DOWN | HALF_EVEN | UNNECESSARY
  deriving DecidableEq, Repr, Inhabited

namespace RoundingMode
def ordinal : RoundingMode → Nat
  | UP => 0 | DOWN => 1 | CEILING => 2 | FLOOR => 3
  | HALF_UP => 4 | HALF_DOWN => 5 | HALF_EVEN => 6 | UNNECESSARY => 7
def ofOrdinal? : Nat → Option RoundingMode
  | 0 => some UP | 1 => some DOWN | 2 => some CEILING | 3 => some FLOOR
  | 4 => some HALF_UP | 5 => some HALF_DOWN | 6 => some HALF_EVEN | 7 => some UNNECESSARY
  | _ => none
def ofName? : String → Option RoundingMode
  | "UP" => some UP | "DOWN" => some DOWN | "CEILING" => some CEILING | "FLOOR" => some FLOOR
  | "HALF_UP" => some HALF_UP | "HALF_DOWN" => some HALF_DOWN | "HALF_EVEN" => some HALF_EVEN
  | "UNNECESSARY" => some UNNECESSARY | _ => none
def name : RoundingMode → String
  | UP => "UP" | DOWN => "DOWN" | CEILING => "CEILING" | FLOOR => "FLOOR"
  | HALF_UP => "HALF_UP" | HALF_DOWN => "HALF_DOWN" | HALF_EVEN => "HALF_EVEN"
  | UNNECESSARY => "UNNECESSARY"
end RoundingMode

/-- Integer division `n / d` (`d ≠ 0`) rounded with a rounding mode;
    `none` for `UNNECESSARY` when the division is inexact. -/
def divRound (n d : Int) (rm : RoundingMode) : Option Int :=
  let q := n.tdiv d
  let r := n.tmod d
  if r = 0 then some q
  else
    let sgn : Int := if (n < 0) = (d < 0) then 1 else -1
    let twice := 2 * r.natAbs
    match rm with
    | .UP => some (q + sgn)
    | .DOWN => some q
    | .CEILING => some (if sgn > 0 then q + 1 else q)
    | .FLOOR => some (if sgn < 0 then q - 1 else q)
    | .HALF_UP => some (if twice ≥ d.natAbs then q + sgn else q)
    | .HALF_DOWN => some (if twice > d.natAbs then q + sgn else q)
    | .HALF_EVEN =>
      some (if twice > d.natAbs ∨ (twice = d.natAbs ∧ q % 2 ≠ 0) then q + sgn else q)
    | .UNNECESSARY => none

/-- Number of decimal digits of a natural number (`digits 0 = 1`). -/
def decDigits (n : Nat) : Nat := if n < 10 then 1 else decDigits (n / 10) + 1

/-- Number of trailing decimal zeros of a nonzero natural number. -/
def trailingZeros (n : Nat) : Nat :=
  if h : n ≠ 0 ∧ n % 10 = 0 then
    have : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h.1) (by decide)
    trailingZeros (n / 10) + 1
  else 0

def pow10Int (k : Nat) : Int := (10 : Int) ^ k

/-- `java.math.MathContext`: precision (0 = unlimited) and rounding mode. -/
structure MathCtx where
  prec : Nat
  rm : RoundingMode
  deriving DecidableEq, Repr, Inhabited

namespace MathCtx
def UNLIMITED : MathCtx := ⟨0, .HALF_UP⟩
def DECIMAL32 : MathCtx := ⟨7, .HALF_EVEN⟩
def DECIMAL64 : MathCtx := ⟨16, .HALF_EVEN⟩
def DECIMAL128 : MathCtx := ⟨34, .HALF_EVEN⟩
end MathCtx

structure BigDec where
  unscaled : Int
  scale : Int
  deriving DecidableEq, Repr, Inhabited

namespace BigDec

/-- The mathematical value. -/
def toRat (d : BigDec) : Rat := (d.unscaled : Rat) * pow10 (-d.scale)

def ofInt (i : Int) : BigDec := ⟨i, 0⟩
def zero : BigDec := ⟨0, 0⟩
def one : BigDec := ⟨1, 0⟩
def ten : BigDec := ⟨10, 0⟩

/-- `unscaled` rescaled to the (larger) scale `s` -/
def upscale (d : BigDec) (s : Int) : Int := d.unscaled * pow10Int (s - d.scale).toNat

def add (x y : BigDec) : BigDec :=
  let s := max x.scale y.scale
  ⟨x.upscale s + y.upscale s, s⟩
def negate (x : BigDec) : BigDec := ⟨-x.unscaled, x.scale⟩
def sub (x y : BigDec) : BigDec := add x y.negate
def mul (x y : BigDec) : BigDec := ⟨x.unscaled * y.unscaled, x.scale + y.scale⟩
def abs (x : BigDec) : BigDec := ⟨x.unscaled.natAbs, x.scale⟩
def signum (x : BigDec) : Int := if x.unscaled > 0 then 1 else if x.unscaled < 0 then -1 else 0
def precision (x : BigDec) : Nat := decDigits x.unscaled.natAbs

/-- `compareTo`: numerical comparison, ignoring scale (`2.0` and `2.00` compare equal). -/
def compareTo (x y : BigDec) : Int :=
  let s := max x.scale y.scale
  let a := x.upscale s
  let b := y.upscale s
  if a < b then -1 else if a = b then 0 else 1

def max (x y : BigDec) : BigDec := if compareTo x y ≥ 0 then x else y
def min (x y : BigDec) : BigDec := if compareTo x y ≤ 0 then x else y

/-- `setScale(newScale, roundingMode)` -/
def setScale (x : BigDec) (s : Int) (rm : RoundingMode) : Option BigDec :=
  if x.scale ≤ s then some ⟨x.upscale s, s⟩
  else (divRound x.unscaled (pow10Int (x.scale - s).toNat) rm).map (⟨·, s⟩)

/-- `divide(divisor, scale, roundingMode)`; `none` for division by zero or a
    required-but-forbidden rounding. -/
def divScale (x y : BigDec) (s : Int) (rm : RoundingMode) : Option BigDec :=
  if y.unscaled = 0 then none
  else
    let e := s - x.scale + y.scale
    let q := if 0 ≤ e then divRound (x.unscaled * pow10Int e.toNat) y.unscaled rm
             else divRound x.unscaled (y.unscaled * pow10Int (-e).toNat) rm
    q.map (⟨·, s⟩)

/-- Round to `prec` significant digits (Java's `doRound`). -/
def roundPrec (x : BigDec) (mc : MathCtx) : Option BigDec :=
  if mc.prec = 0 then some x
  else
    let p := x.precision
    if p ≤ mc.prec then some x
    else
      let drop := p - mc.prec
      match divRound x.unscaled (pow10Int drop) mc.rm with
      | none => none
      | some u =>
        if decDigits u.natAbs > mc.prec then some ⟨u / 10, x.scale - drop - 1⟩
        else some ⟨u, x.scale - drop⟩

/-- Remove trailing zeros while the scale stays above `pref`. -/
def stripTo (x : BigDec) (pref : Int) : BigDec :=
  if x.unscaled = 0 then x
  else
    let tz : Int := trailingZeros x.unscaled.natAbs
    let k := Min.min tz (x.scale - pref)
    if k ≤ 0 then x else ⟨x.unscaled / pow10Int k.toNat, x.scale - k⟩

/-- `stripTrailingZeros()` (JDK 8+: zero becomes `BigDecimal.ZERO`). -/
def stripTrailingZeros (x : BigDec) : BigDec :=
  if x.unscaled = 0 then zero
  else let tz := trailingZeros x.unscaled.natAbs
    ⟨x.unscaled / pow10Int tz, x.scale - tz⟩

/-- Exact decimal representation of a rational with a terminating expansion:
    the smallest scale `s` with `q * 10^s` integral, if any. -/
def minScaleOf (q : Rat) : Option Int :=
  -- the reduced denominator must be 2^a 5^b; then s = max(a, b) (minus trailing zeros
  -- of the numerator when q is an integer)
  let den := q.den
  let rec strip (n p : Nat) (fuel : Nat) : Nat × Nat :=
    match fuel with
    | 0 => (n, 0)
    | fuel + 1 => if n % p = 0 ∧ n > 1 then let r := strip (n / p) p fuel; (r.1, r.2 + 1) else (n, 0)
  let (d1, a) := strip den 2 (den + 1)
  let (d2, b) := strip d1 5 (d1 + 1)
  if d2 ≠ 1 then none
  else if den = 1 then
    if q.num = 0 then some 0 else some (-(trailingZeros q.num.natAbs : Int))
  else some (Nat.max a b)

/-- The BigDecimal with value `q` (terminating) and scale `s` (must be ≥ minScaleOf q). -/
def ofRatAtScale (q : Rat) (s : Int) : BigDec :=
  ⟨(q * pow10 s).floor, s⟩

/-- `divide(divisor)` (exact): `none` if the divisor is zero or the quotient does not
    terminate. Result scale: the preferred scale `this.scale - divisor.scale` or the
    smallest larger scale that represents the quotient exactly. -/
def divExact (x y : BigDec) : Option BigDec :=
  if y.unscaled = 0 then none
  else
    let pref := x.scale - y.scale
    if x.unscaled = 0 then some ⟨0, pref⟩
    else
      let q := x.toRat / y.toRat
      match minScaleOf q with
      | none => none
      | some ms => some (ofRatAtScale q (Max.max pref ms))

/-- `divide(divisor, mc)`. -/
def divMC (x y : BigDec) (mc : MathCtx) : Option BigDec :=
  if mc.prec = 0 then divExact x y
  else if y.unscaled = 0 then none
  else
    let pref := x.scale - y.scale
    if x.unscaled = 0 then some ⟨0, pref⟩
    else
      let q := x.toRat / y.toRat
      match minScaleOf q with
      | some ms =>
        -- exact quotient: if it fits in prec digits, use the scale closest to pref
        let d := ofRatAtScale q ms
        if d.precision ≤ mc.prec then
          if ms ≥ pref then some d
          else
            let room : Int := (mc.prec : Int) - d.precision
            some (ofRatAtScale q (ms + Min.min room (pref - ms)))
        else roundPrec d mc
      | none =>
        -- non-terminating: compute enough digits, then round (the exact remainder decides
        -- ties, so take one more digit than needed plus a sticky correction)
        let a := if q < 0 then -q else q
        let e0 : Int := (decDigits a.num.natAbs : Int) - (decDigits a.den : Int)
        -- choose scale s so that q * 10^s has at least prec + 2 integer digits
        let s : Int := (mc.prec : Int) + 2 - e0
        let t := a * pow10 s
        let fl := t.floor
        -- t is never integral here (non-terminating), so a sticky last digit decides
        -- every rounding exactly as the infinite expansion would
        let sticky : Int := fl * 10 + 1
        roundPrec ⟨if q < 0 then -sticky else sticky, s + 1⟩ mc

/-- `divideToIntegralValue(divisor)`. -/
def divToIntegral (x y : BigDec) : Option BigDec :=
  if y.unscaled = 0 then none
  else
    let pref := x.scale - y.scale
    let t := ratTrunc (x.toRat / y.toRat)
    if t = 0 then some ⟨0, pref⟩
    else if 0 ≤ pref then some ⟨t * pow10Int pref.toNat, pref⟩
    else
      let tz : Int := trailingZeros t.natAbs
      let k := Min.min tz (-pref)
      some ⟨t / pow10Int k.toNat, -k⟩

/-- `remainder(divisor)` = `this - this.divideToIntegralValue(divisor) * divisor`. -/
def remainder (x y : BigDec) : Option BigDec :=
  (divToIntegral x y).map fun t => sub x (mul t y)

/-- `pow(n)`, `0 ≤ n ≤ 999999999`. -/
def pow (x : BigDec) (n : Int) : Option BigDec :=
  if n < 0 ∨ n > 999999999 then none else some ⟨x.unscaled ^ n.toNat, x.scale * n⟩

def movePointLeft (x : BigDec) (n : Int) : BigDec :=
  let r : BigDec := ⟨x.unscaled, x.scale + n⟩
  if r.scale < 0 then ⟨r.upscale 0, 0⟩ else r
def movePointRight (x : BigDec) (n : Int) : BigDec := movePointLeft x (-n)
def scaleByPowerOfTen (x : BigDec) (n : Int) : BigDec := ⟨x.unscaled, x.scale - n⟩

/-- `toBigInteger()`: truncation toward zero. -/
def toBigInt (x : BigDec) : Int := ratTrunc x.toRat

/-- `intValueExact()` / `longValueExact()` -/
def toIntExact (w : Nat) (x : BigDec) : Option Int :=
  let t := x.toBigInt
  if (t : Rat) ≠ x.toRat then none
  else if t < -((2 ^ (w - 1) : Nat) : Int) ∨ t ≥ ((2 ^ (w - 1) : Nat) : Int) then none
  else some t

/-! ### String conversions -/

def digitsOf (n : Nat) : List Char := (toString n).toList

/-- `toString()` (scientific notation when the adjusted exponent is below -6 or the scale
    is negative), exactly as `BigDecimal.layoutChars(true)`. -/
def toJavaString (x : BigDec) : String :=
  let coeff := digitsOf x.unscaled.natAbs
  let sign := if x.unscaled < 0 then "-" else ""
  if x.scale = 0 then sign ++ String.ofList coeff
  else
    let len : Int := coeff.length
    let adjusted : Int := -x.scale + (len - 1)
    if 0 ≤ x.scale ∧ adjusted ≥ -6 then
      let pad := x.scale - len
      if 0 ≤ pad then
        sign ++ "0." ++ String.ofList (List.replicate pad.toNat '0') ++ String.ofList coeff
      else
        let ip := (-pad).toNat
        sign ++ String.ofList (coeff.take ip) ++ "." ++ String.ofList (coeff.drop ip)
    else
      let mant := match coeff with
        | c :: rest@(_ :: _) => String.ofList (c :: '.' :: rest)
        | cs => String.ofList cs
      let ex := if adjusted = 0 then "" else
        "E" ++ (if adjusted > 0 then "+" else "") ++ toString adjusted
      sign ++ mant ++ ex

/-- `toPlainString()` -/
def toPlainString (x : BigDec) : String :=
  let coeff := digitsOf x.unscaled.natAbs
  let neg := x.unscaled < 0
  if x.scale = 0 then toString x.unscaled
  else if x.scale < 0 then
    if x.unscaled = 0 then "0"
    else (if neg then "-" else "") ++ String.ofList coeff ++
      String.ofList (List.replicate (-x.scale).toNat '0')
  else
    let ip : Int := (coeff.length : Int) - x.scale
    let sgn := if neg then "-" else ""
    if ip = 0 then sgn ++ "0." ++ String.ofList coeff
    else if 0 < ip then
      sgn ++ String.ofList (coeff.take ip.toNat) ++ "." ++ String.ofList (coeff.drop ip.toNat)
    else sgn ++ "0." ++ String.ofList (List.replicate (-ip).toNat '0') ++ String.ofList coeff

/-- Value of a list of decimal digit characters (kernel-friendly, no `String` conversion). -/
def digitsVal (cs : List Char) : Nat := cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- `new BigDecimal(String)`; `none` = `NumberFormatException`. -/
def parse? (s : String) : Option BigDec :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let isD : Char → Bool := Char.isDigit
  let intPart := cs.takeWhile isD
  let cs := cs.dropWhile isD
  let (fracPart, cs) := match cs with
    | '.' :: r => (r.takeWhile isD, r.dropWhile isD)
    | r => ([], r)
  if intPart.isEmpty ∧ fracPart.isEmpty then none
  else
    let expo : Option Int := match cs with
      | [] => some 0
      | c :: r =>
        if c = 'e' ∨ c = 'E' then
          let (eneg, r) := match r with
            | '-' :: r' => (true, r')
            | '+' :: r' => (false, r')
            | r' => (false, r')
          if r.isEmpty ∨ ¬ r.all isD then none
          else
            let v : Int := digitsVal r
            some (if eneg then -v else v)
        else none
    match expo with
    | none => none
    | some ex =>
      let mag : Int := digitsVal (intPart ++ fracPart)
      some ⟨if neg then -mag else mag, (fracPart.length : Int) - ex⟩

/-- `BigDecimal.hashCode()`: `31 * unscaledValue().hashCode() + scale`, where
    `BigInteger.hashCode` folds the big-endian 32-bit magnitude words. -/
def bigIntHash (i : Int) : I32 :=
  let rec words (n : Nat) (fuel : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if n = 0 then acc else words (n / 2 ^ 32) fuel ((n % 2 ^ 32) :: acc)
  let ws := words i.natAbs (i.natAbs + 1) []
  let h : I32 := ws.foldl (fun h w => h * 31 + BitVec.ofNat 32 w) 0
  if i < 0 then -h else h

def hashCode (x : BigDec) : I32 := 31 * bigIntHash x.unscaled + BitVec.ofInt 32 x.scale

/-- `new BigDecimal(double)`: the exact binary value, minimal scale. `none` for NaN/∞. -/
def ofDoubleExact (bits : BitVec 64) : Option BigDec :=
  match FVal.decode .double bits.toNat with
  | .nan | .inf _ => none
  | .zero _ => some zero
  | .num q =>
    match minScaleOf q with
    | some s => some (ofRatAtScale q (Max.max s 0))
    | none => none

end BigDec

end Jimple
