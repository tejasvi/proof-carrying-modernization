/-
  Jimple/Numeric.lean

  Java primitive arithmetic.

  * `int`/`long` (and `boolean`, `byte`, `short`, `char`, which the JVM computes as `int`)
    are two's-complement bit vectors (`BitVec 32`, `BitVec 64`), so `bv_decide`,
    `bv_omega` and the `BitVec.toInt` lemmas apply directly.
  * `float`/`double` are IEEE-754 binary32/binary64 bit patterns. Their arithmetic is
    defined *exactly*: decode to an exact rational (or a special value), compute the exact
    result in `Rat`, then round to nearest-even. This is the IEEE-754 definition and
    Java's semantics since JDK 17 (JEP 306, all floating point strict), and it keeps
    floating point provable through `Rat`.
-/
import Jimple.Syntax

namespace Jimple

abbrev I32 := BitVec 32
abbrev I64 := BitVec 64

/-! ## int / long -/

namespace JInt
def MIN : I32 := BitVec.ofInt 32 (-2147483648)
def MAX : I32 := BitVec.ofInt 32 2147483647
def ofBool (b : Bool) : I32 := if b then 1 else 0
def shl (a b : I32) : I32 := a <<< (b.toNat % 32)
def shr (a b : I32) : I32 := a.sshiftRight (b.toNat % 32)
def ushr (a b : I32) : I32 := a >>> (b.toNat % 32)
/-- `i2b`, `i2s`, `i2c`: narrowing then widening back to `int` -/
def toByte (a : I32) : I32 := (a.setWidth 8).signExtend 32
def toShort (a : I32) : I32 := (a.setWidth 16).signExtend 32
def toChar (a : I32) : I32 := (a.setWidth 16).zeroExtend 32
def toLong (a : I32) : I64 := a.signExtend 64
end JInt

namespace JLong
def MIN : I64 := BitVec.ofInt 64 (-9223372036854775808)
def MAX : I64 := BitVec.ofInt 64 9223372036854775807
def shl (a : I64) (b : I32) : I64 := a <<< (b.toNat % 64)
def shr (a : I64) (b : I32) : I64 := a.sshiftRight (b.toNat % 64)
def ushr (a : I64) (b : I32) : I64 := a >>> (b.toNat % 64)
def toInt (a : I64) : I32 := a.setWidth 32
/-- `lcmp` -/
def cmp (a b : I64) : I32 :=
  if a.slt b then -1 else if a = b then 0 else 1
end JLong

/-- Clamp an integer into the signed range of `w` bits (used by float-to-integer casts). -/
def clampInt (w : Nat) (x : Int) : Int :=
  let lo : Int := -(2 ^ (w - 1) : Nat)
  let hi : Int := (2 ^ (w - 1) : Nat) - 1
  if x < lo then lo else if x > hi then hi else x

/-! ## IEEE-754 binary floating point, defined through exact rationals -/

/-- `2^k` for an integer exponent. -/
def pow2 (k : Int) : Rat :=
  if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/-- `10^k` for an integer exponent. -/
def pow10 (k : Int) : Rat :=
  if 0 ≤ k then ((10 ^ k.toNat : Nat) : Rat) else 1 / ((10 ^ (-k).toNat : Nat) : Rat)

/-- Truncation toward zero of a rational. -/
def ratTrunc (q : Rat) : Int := if 0 ≤ q then q.floor else q.ceil

/-- Round half to even of a non-negative rational. -/
def ratRoundHalfEven (t : Rat) : Int :=
  let fl := t.floor
  let r := t - fl
  if r > 1/2 then fl + 1 else if r < 1/2 then fl else if fl % 2 = 0 then fl else fl + 1

structure FFmt where
  ebits : Nat
  fbits : Nat
  deriving DecidableEq, Repr

namespace FFmt
def single : FFmt := ⟨8, 23⟩
def double : FFmt := ⟨11, 52⟩
def bias (f : FFmt) : Int := ((2 ^ (f.ebits - 1) : Nat) : Int) - 1
def emin (f : FFmt) : Int := 1 - f.bias
def expMask (f : FFmt) : Nat := 2 ^ f.ebits - 1
def signBit (f : FFmt) : Nat := 2 ^ (f.ebits + f.fbits)
def infBits (f : FFmt) (neg : Bool) : Nat :=
  (if neg then f.signBit else 0) + f.expMask * 2 ^ f.fbits
/-- canonical quiet NaN (Java's `Double.NaN` / `Float.NaN`) -/
def nanBits (f : FFmt) : Nat := f.expMask * 2 ^ f.fbits + 2 ^ (f.fbits - 1)
end FFmt

/-- A decoded floating-point value; `num q` is a nonzero finite value, exactly. -/
inductive FVal where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | num (q : Rat)
  deriving DecidableEq, Repr, Inhabited

namespace FVal

def decode (f : FFmt) (bits : Nat) : FVal :=
  let frac := bits % 2 ^ f.fbits
  let e := (bits / 2 ^ f.fbits) % 2 ^ f.ebits
  let neg := (bits / f.signBit) % 2 = 1
  let sgn : Rat := if neg then -1 else 1
  if e = f.expMask then (if frac = 0 then .inf neg else .nan)
  else if e = 0 then
    (if frac = 0 then .zero neg else .num (sgn * (frac : Rat) * pow2 (f.emin - f.fbits)))
  else .num (sgn * ((2 ^ f.fbits + frac : Nat) : Rat) * pow2 ((e : Int) - f.bias - f.fbits))

/-- Round a nonzero rational to the nearest representable value (ties to even). -/
def roundBits (f : FFmt) (q : Rat) : Nat :=
  let neg := decide (q < 0)
  let a : Rat := if neg then -q else q
  let sign : Nat := if neg then f.signBit else 0
  let e0 : Int := (Nat.log2 a.num.toNat : Int) - (Nat.log2 a.den : Int)
  let e : Int := if a < pow2 e0 then e0 - 1 else e0
  let qe : Int := max e f.emin - f.fbits
  let m0 := (ratRoundHalfEven (a / pow2 qe)).toNat
  if m0 = 0 then sign
  else
    let (m, qe) := if m0 ≥ 2 ^ (f.fbits + 1) then (m0 / 2, qe + 1) else (m0, qe)
    if m < 2 ^ f.fbits then sign + m
    else
      let ef : Int := qe + f.fbits + f.bias
      if ef ≥ f.expMask then f.infBits neg
      else sign + ef.toNat * 2 ^ f.fbits + (m - 2 ^ f.fbits)

def encode (f : FFmt) : FVal → Nat
  | .nan => f.nanBits
  | .inf neg => f.infBits neg
  | .zero neg => if neg then f.signBit else 0
  | .num q => if q = 0 then 0 else roundBits f q

def neg : FVal → FVal
  | .nan => .nan
  | .inf n => .inf !n
  | .zero n => .zero !n
  | .num q => .num (-q)

def isNeg : FVal → Bool
  | .inf n | .zero n => n
  | .num q => decide (q < 0)
  | .nan => false

/-- exact sum (before rounding); exact zero sums of nonzero operands are `+0` -/
def add : FVal → FVal → FVal
  | .nan, _ | _, .nan => .nan
  | .inf a, .inf b => if a = b then .inf a else .nan
  | .inf a, _ => .inf a
  | _, .inf b => .inf b
  | .zero a, .zero b => .zero (a && b)
  | .zero _, .num q => .num q
  | .num p, .zero _ => .num p
  | .num p, .num q => if p + q = 0 then .zero false else .num (p + q)

def mul : FVal → FVal → FVal
  | .nan, _ | _, .nan => .nan
  | .inf _, .zero _ | .zero _, .inf _ => .nan
  | x, y =>
    let s := x.isNeg != y.isNeg
    match x, y with
    | .inf _, _ | _, .inf _ => .inf s
    | .zero _, _ | _, .zero _ => .zero s
    | .num p, .num q => .num (p * q)
    | _, _ => .nan

def div : FVal → FVal → FVal
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .zero _, .zero _ => .nan
  | x, y =>
    let s := x.isNeg != y.isNeg
    match x, y with
    | .inf _, _ => .inf s
    | _, .inf _ => .zero s
    | .zero _, _ => .zero s
    | _, .zero _ => .inf s
    | .num p, .num q => .num (p / q)
    | _, _ => .nan

/-- Java `%` on floating point (C `fmod`: truncated quotient, sign of the dividend) -/
def rem : FVal → FVal → FVal
  | .nan, _ | _, .nan => .nan
  | .inf _, _ => .nan
  | _, .zero _ => .nan
  | x, .inf _ => x
  | .zero n, _ => .zero n
  | .num p, .num q =>
    let r := p - (ratTrunc (p / q) : Rat) * q
    if r = 0 then .zero (decide (p < 0)) else .num r

/-- `fcmpl`/`dcmpl` (`nanResult = -1`) and `fcmpg`/`dcmpg` (`nanResult = 1`) -/
def cmp (nanResult : I32) : FVal → FVal → I32
  | .nan, _ | _, .nan => nanResult
  | x, y =>
    let v : FVal → Rat := fun | .num q => q | .zero _ => 0 | _ => 0
    match x, y with
    | .inf a, .inf b => if a = b then 0 else if a then -1 else 1
    | .inf a, _ => if a then -1 else 1
    | _, .inf b => if b then 1 else -1
    | _, _ => if v x < v y then -1 else if v x = v y then 0 else 1

/-- float/double to integer (`f2i`, `d2l`, ...): NaN ↦ 0, saturating, toward zero -/
def toIntSat (w : Nat) : FVal → Int
  | .nan => 0
  | .zero _ => 0
  | .inf n => if n then clampInt w (-(2 ^ w : Nat)) else clampInt w (2 ^ w : Nat)
  | .num q => clampInt w (ratTrunc q)

def ofInt (i : Int) : FVal := if i = 0 then .zero false else .num i

end FVal

/-! Operations on Java `float` (binary32) and `double` (binary64) bit patterns. -/
namespace JFloat
open FVal
def dec32 (x : BitVec 32) : FVal := decode .single x.toNat
def dec64 (x : BitVec 64) : FVal := decode .double x.toNat
def enc32 (v : FVal) : BitVec 32 := BitVec.ofNat 32 (encode .single v)
def enc64 (v : FVal) : BitVec 64 := BitVec.ofNat 64 (encode .double v)

def fadd (a b : BitVec 32) : BitVec 32 := enc32 ((dec32 a).add (dec32 b))
def fsub (a b : BitVec 32) : BitVec 32 := enc32 ((dec32 a).add (dec32 b).neg)
def fmul (a b : BitVec 32) : BitVec 32 := enc32 ((dec32 a).mul (dec32 b))
def fdiv (a b : BitVec 32) : BitVec 32 := enc32 ((dec32 a).div (dec32 b))
def frem (a b : BitVec 32) : BitVec 32 := enc32 ((dec32 a).rem (dec32 b))
/-- negation flips the sign bit (also of NaN), as the JVM does -/
def fneg (a : BitVec 32) : BitVec 32 := a ^^^ BitVec.ofNat 32 FFmt.single.signBit
def dadd (a b : BitVec 64) : BitVec 64 := enc64 ((dec64 a).add (dec64 b))
def dsub (a b : BitVec 64) : BitVec 64 := enc64 ((dec64 a).add (dec64 b).neg)
def dmul (a b : BitVec 64) : BitVec 64 := enc64 ((dec64 a).mul (dec64 b))
def ddiv (a b : BitVec 64) : BitVec 64 := enc64 ((dec64 a).div (dec64 b))
def drem (a b : BitVec 64) : BitVec 64 := enc64 ((dec64 a).rem (dec64 b))
def dneg (a : BitVec 64) : BitVec 64 := a ^^^ BitVec.ofNat 64 FFmt.double.signBit

def fcmpl (a b : BitVec 32) : I32 := cmp (-1) (dec32 a) (dec32 b)
def fcmpg (a b : BitVec 32) : I32 := cmp 1 (dec32 a) (dec32 b)
def dcmpl (a b : BitVec 64) : I32 := cmp (-1) (dec64 a) (dec64 b)
def dcmpg (a b : BitVec 64) : I32 := cmp 1 (dec64 a) (dec64 b)

def i2f (a : I32) : BitVec 32 := enc32 (ofInt a.toInt)
def i2d (a : I32) : BitVec 64 := enc64 (ofInt a.toInt)
def l2f (a : I64) : BitVec 32 := enc32 (ofInt a.toInt)
def l2d (a : I64) : BitVec 64 := enc64 (ofInt a.toInt)
def f2i (a : BitVec 32) : I32 := BitVec.ofInt 32 ((dec32 a).toIntSat 32)
def f2l (a : BitVec 32) : I64 := BitVec.ofInt 64 ((dec32 a).toIntSat 64)
def d2i (a : BitVec 64) : I32 := BitVec.ofInt 32 ((dec64 a).toIntSat 32)
def d2l (a : BitVec 64) : I64 := BitVec.ofInt 64 ((dec64 a).toIntSat 64)
def f2d (a : BitVec 32) : BitVec 64 := enc64 (dec32 a)
def d2f (a : BitVec 64) : BitVec 32 := enc32 (dec64 a)

def isNaN32 (a : BitVec 32) : Bool := dec32 a = .nan
def isNaN64 (a : BitVec 64) : Bool := dec64 a = .nan

/-- Exact decimal `m * 10^e` correctly rounded to binary64 / binary32 (literal parsing). -/
def decimalToDouble (neg : Bool) (m : Nat) (e : Int) : BitVec 64 :=
  enc64 (if m = 0 then .zero neg else .num ((if neg then -1 else 1) * (m : Rat) * pow10 e))
def decimalToFloat (neg : Bool) (m : Nat) (e : Int) : BitVec 32 :=
  enc32 (if m = 0 then .zero neg else .num ((if neg then -1 else 1) * (m : Rat) * pow10 e))

def posInf64 : BitVec 64 := BitVec.ofNat 64 (FFmt.double.infBits false)
def negInf64 : BitVec 64 := BitVec.ofNat 64 (FFmt.double.infBits true)
def nan64 : BitVec 64 := BitVec.ofNat 64 FFmt.double.nanBits
def posInf32 : BitVec 32 := BitVec.ofNat 32 (FFmt.single.infBits false)
def negInf32 : BitVec 32 := BitVec.ofNat 32 (FFmt.single.infBits true)
def nan32 : BitVec 32 := BitVec.ofNat 32 FFmt.single.nanBits

end JFloat

end Jimple
