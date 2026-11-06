/-
StrictTS: exact model of the ECMAScript Number type (IEEE-754 binary64).

Every value of `F64` is a distinct ECMAScript Number value: one NaN, two infinities,
two zeros, and the canonical finite values. Lean equality on `F64` is therefore
`Object.is` (SameValue); the IEEE comparisons used by `===`, `<`, ... are separate functions.

All operations are computed exactly on integers and rounded once with `F64.round`
(round-half-to-even). Computational paths use shifts rather than large powers of two so that
`by decide` works on small concrete examples; facts about these definitions are in
`StrictTS.Num.F64Lemmas`.
-/

namespace StrictTS

/-- Canonical finite binary64 value `(-1)^neg * man * 2^exp`:
* normal:            `2^52 ≤ man < 2^53` and `-1074 ≤ exp ≤ 971`
* subnormal or zero: `man < 2^52` and `exp = -1074`.
Each finite double (including `+0` and `-0`) has exactly one such representation. -/
structure Fin64 where
  neg : Bool
  man : Nat
  exp : Int
  valid : (2^52 ≤ man ∧ man < 2^53 ∧ -1074 ≤ exp ∧ exp ≤ 971) ∨ (man < 2^52 ∧ exp = -1074)
  deriving DecidableEq

/-- ECMAScript Number values. -/
inductive F64 where
  | nan
  | inf (neg : Bool)
  | fin (x : Fin64)
  deriving DecidableEq

namespace F64

instance : Inhabited F64 := ⟨.nan⟩

/-- Number of significant bits of `n` (`0` for `0`). -/
def bitLen (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- Smart constructor. The validity test always succeeds for the arguments produced by
`round`; the `nan` fallback is unreachable and only avoids proof terms in the algorithm. -/
def mkFin (neg : Bool) (man : Nat) (exp : Int) : F64 :=
  if h : (2^52 ≤ man ∧ man < 2^53 ∧ -1074 ≤ exp ∧ exp ≤ 971) ∨ (man < 2^52 ∧ exp = -1074) then
    .fin ⟨neg, man, exp, h⟩
  else .nan

/-- Round `(-1)^neg * (m + δ) * 2^e` to binary64, round-half-to-even, where `δ = 0` when
`sticky = false` and `0 < δ < 1` when `sticky = true`.

Precondition when `sticky = true`: at least two bits of `m` lie below the last bit of the
result, i.e. `e + 2 ≤ q` for the result quantum exponent `q = max (E - 52) (-1074)` with
`E = e + bitLen m - 1` (callers guarantee this by producing ≥ 55 significant bits and
`e ≤ -1076`). An exact zero (`m = 0`, `sticky = false`) gives the zero of sign `neg`.
Results beyond the finite range give `±Infinity`. -/
def round (neg : Bool) (m : Nat) (e : Int) (sticky : Bool := false) : F64 :=
  if m = 0 ∧ sticky = false then mkFin neg 0 (-1074)
  else
    let E : Int := e + (bitLen m : Int) - 1
    let q : Int := max (E - 52) (-1074)
    if q ≤ e then
      if q > 971 then .inf neg else mkFin neg (m * 2 ^ (e - q).toNat) q
    else
      let s : Nat := (q - e).toNat
      let man0 := m >>> s
      let rem := m % 2 ^ s
      let half := 2 ^ (s - 1)
      let up : Bool := if sticky then decide (half ≤ rem)
        else decide (half < rem) || (decide (rem = half) && man0 % 2 == 1)
      let man1 := if up then man0 + 1 else man0
      let man2 := if man1 = 2 ^ 53 then 2 ^ 52 else man1
      let q2 := if man1 = 2 ^ 53 then q + 1 else q
      if q2 > 971 then .inf neg else mkFin neg man2 q2

/-- `+0` and `-0`. -/
def zero (neg : Bool := false) : F64 := mkFin neg 0 (-1074)

/-- Nearest double to an integer (round-half-even); exact when `|n| ≤ 2^53`. -/
def ofInt (n : Int) : F64 := round (n < 0) n.natAbs 0

/-- Nearest double to a natural number. -/
def ofNat (n : Nat) : F64 := round false n 0

instance (n : Nat) : OfNat F64 n := ⟨ofNat n⟩

end F64

namespace Fin64

/-- `(-1)^neg * man * 2^k` as an integer. -/
def sint (x : Fin64) (k : Nat) : Int :=
  if x.neg then -((x.man <<< k : Nat) : Int) else ((x.man <<< k : Nat) : Int)

/-- The smaller exponent of `x` and `y`; `x = sint x (x.exp - minExp x y).toNat * 2^(minExp x y)`. -/
def minExp (x y : Fin64) : Int := if x.exp ≤ y.exp then x.exp else y.exp

/-- Signed integer significands of `x` and `y` over the common exponent `minExp x y`. -/
def ints (x y : Fin64) : Int × Int :=
  (x.sint (x.exp - minExp x y).toNat, y.sint (y.exp - minExp x y).toNat)

/-- `⌊|x|⌋`. -/
def intMag (x : Fin64) : Nat :=
  if 0 ≤ x.exp then x.man <<< x.exp.toNat else x.man >>> (-x.exp).toNat

/-- Fractional part of `|x|` scaled by `2^k`, `k = max 0 (-exp)`:
`|x| = intMag x + fracMag x / 2^k`. Zero iff `x` is an integer. -/
def fracMag (x : Fin64) : Nat :=
  x.man - ((x.man >>> (-x.exp).toNat) <<< (-x.exp).toNat)

/-- One half scaled by `2^(-exp)` (used only when `fracMag x ≠ 0`, which forces `exp < 0`). -/
def halfMag (x : Fin64) : Nat := 1 <<< ((-x.exp).toNat - 1)

end Fin64

namespace F64

/-! ## Constants -/

def posInf : F64 := .inf false
def negInf : F64 := .inf true
def posZero : F64 := zero false
def negZero : F64 := zero true
def one : F64 := ofNat 1
/-- `Number.MAX_VALUE = (2^53 - 1) * 2^971`. -/
def maxValue : F64 := mkFin false (2^53 - 1) 971
/-- `Number.MIN_VALUE = 2^-1074` (5e-324). -/
def minValue : F64 := mkFin false 1 (-1074)
/-- `Number.EPSILON = 2^-52`. -/
def epsilon : F64 := mkFin false (2^52) (-104)
/-- `Number.MAX_SAFE_INTEGER = 2^53 - 1`. -/
def maxSafeInteger : F64 := ofNat (2^53 - 1)
/-- `Number.MIN_SAFE_INTEGER = -(2^53 - 1)`. -/
def minSafeInteger : F64 := ofInt (-(2^53 - 1))

/-! ## Classification -/

/-- `Number.isNaN`. -/
def isNaN : F64 → Bool
  | .nan => true
  | _ => false

/-- `Number.isFinite`. -/
def isFinite : F64 → Bool
  | .fin _ => true
  | _ => false

/-- `x` is `+0` or `-0`. -/
def isZero : F64 → Bool
  | .fin x => x.man == 0
  | _ => false

/-- Sign bit: true for `-0`, negative numbers and `-Infinity`; false for NaN. -/
def signBit : F64 → Bool
  | .nan => false
  | .inf neg => neg
  | .fin x => x.neg

/-! ## Exact integer views -/

/-- `some n` iff the value is finite and the integer `n` (`±0 ↦ 0`). -/
def toInt? : F64 → Option Int
  | .fin x => if x.fracMag = 0 then some (if x.neg then -(x.intMag : Int) else x.intMag) else none
  | _ => none

/-- `BigInt(x)` succeeds iff `x` is integral. -/
abbrev toBigInt? : F64 → Option Int := toInt?

/-- `Number(bigint)`: nearest double, ties to even. -/
abbrev ofBigInt : Int → F64 := ofInt

/-- `Number.isInteger`. -/
def isInteger (x : F64) : Bool := (toInt? x).isSome

/-- `Number.isSafeInteger`: integral and `|x| ≤ 2^53 - 1`. -/
def isSafeInteger (x : F64) : Bool :=
  match toInt? x with
  | some n => decide (n.natAbs ≤ 2^53 - 1)
  | none => false

/-- `truncate(ℝ(x))` for finite `x`, `0` for NaN and `±Infinity` (the integer behind ToInt32 etc.). -/
def truncInt : F64 → Int
  | .fin x => if x.neg then -(x.intMag : Int) else x.intMag
  | _ => 0

/-- Correctly rounded `(-1)^neg * num / den * 2^e` (round-half-even, `±Infinity` on overflow,
signed zero on underflow; an exact zero gets the sign `neg`). `den = 0` gives NaN. -/
def ofFrac (neg : Bool) (num den : Nat) (e : Int) : F64 :=
  if den = 0 then .nan
  else if num = 0 then zero neg
  else
    -- the integer quotient gets at least 55 significant bits, as `round` requires with sticky
    let k : Int := 55 + (bitLen den : Int) - (bitLen num : Int)
    if 0 ≤ k then
      let n := num <<< k.toNat
      round neg (n / den) (e - k) (n % den != 0)
    else
      let d := den <<< (-k).toNat
      round neg (num / d) (e - k) (num % d != 0)

/-! ## Arithmetic (ECMA-262 Number::unaryMinus, add, subtract, multiply, divide, remainder) -/

/-- Number::unaryMinus (flips the sign of zeros and infinities too). -/
def neg : F64 → F64
  | .nan => .nan
  | .inf b => .inf (!b)
  | .fin x => .fin { x with neg := !x.neg }

/-- `Math.abs`. -/
def abs : F64 → F64
  | .nan => .nan
  | .inf _ => .inf false
  | .fin x => .fin { x with neg := false }

/-- Number::add: exact sum rounded once; `x + (-x) = +0`, `(-0) + (-0) = -0`. -/
def add : F64 → F64 → F64
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin _, .nan => .nan
  | .inf a, .inf b => if a = b then .inf a else .nan
  | .inf a, .fin _ => .inf a
  | .fin _, .inf b => .inf b
  | .fin x, .fin y =>
    if x.man = 0 then (if y.man = 0 then zero (x.neg && y.neg) else .fin y)
    else if y.man = 0 then .fin x
    else
      let s := (x.ints y).1 + (x.ints y).2
      round (decide (s < 0)) s.natAbs (x.minExp y)

/-- Number::subtract is `x + (-y)`. -/
def sub (x y : F64) : F64 := add x (neg y)

/-- Number::multiply: exact product rounded once; the sign of a zero result is the xor of the
operand signs (`0 * -3 = -0`, underflow keeps the sign). -/
def mul : F64 → F64 → F64
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin _, .nan => .nan
  | .inf a, .inf b => .inf (a ^^ b)
  | .inf a, .fin y => if y.man = 0 then .nan else .inf (a ^^ y.neg)
  | .fin x, .inf b => if x.man = 0 then .nan else .inf (x.neg ^^ b)
  | .fin x, .fin y => round (x.neg ^^ y.neg) (x.man * y.man) (x.exp + y.exp)

/-- Number::divide: correctly rounded quotient (`ofFrac`); `x / ±0 = ±Infinity`, `0 / 0 = NaN`. -/
def div : F64 → F64 → F64
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin _, .nan => .nan
  | .inf _, .inf _ => .nan
  | .inf a, .fin y => .inf (a ^^ y.neg)
  | .fin x, .inf b => zero (x.neg ^^ b)
  | .fin x, .fin y =>
    if y.man = 0 then (if x.man = 0 then .nan else .inf (x.neg ^^ y.neg))
    else ofFrac (x.neg ^^ y.neg) x.man y.man (x.exp - y.exp)

/-- JS `%`: truncating remainder with the sign of the dividend; always exact. -/
def rem : F64 → F64 → F64
  | .nan, _ => .nan
  | .inf _, _ => .nan
  | .fin _, .nan => .nan
  | .fin x, .inf _ => .fin x
  | .fin x, .fin y =>
    if y.man = 0 then .nan
    else if x.man = 0 then .fin x
    else round x.neg ((x.ints y).1.natAbs % (x.ints y).2.natAbs) (x.minExp y)

instance : Neg F64 := ⟨neg⟩
instance : Add F64 := ⟨add⟩
instance : Sub F64 := ⟨sub⟩
instance : Mul F64 := ⟨mul⟩
instance : Div F64 := ⟨div⟩
instance : Mod F64 := ⟨rem⟩

/-- `⌊√n⌋` by Newton's method from above (explicit fuel; 64 steps suffice far beyond 2^4096). -/
def isqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else go 64 (1 <<< ((bitLen n + 1) / 2))
where
  go : Nat → Nat → Nat
  | 0, g => g
  | fuel + 1, g =>
    let g' := (g + n / g) / 2
    if g' < g then go fuel g' else g

/-- `Math.sqrt`, correctly rounded. -/
def sqrt : F64 → F64
  | .nan => .nan
  | .inf b => if b then .nan else .inf false
  | .fin x =>
    if x.man = 0 then .fin x
    else if x.neg then .nan
    else
      -- `x = m * 2^e` with `e` even; scale by `4^k` so that the root has ≥ 55 bits
      let m := if x.exp % 2 = 0 then x.man else x.man <<< 1
      let e := if x.exp % 2 = 0 then x.exp else x.exp - 1
      let k := (110 - bitLen m) / 2 + 1
      let n := m <<< (2 * k)
      let s := isqrt n
      round false s (e / 2 - (k : Int)) (s * s != n)

/-! ## Comparisons -/

/-- `x < y` (false if either is NaN). -/
def lt : F64 → F64 → Bool
  | .fin x, .fin y => decide ((x.ints y).1 < (x.ints y).2)
  | .inf a, .inf b => a && !b
  | .inf a, .fin _ => a
  | .fin _, .inf b => !b
  | _, _ => false

/-- `x ≤ y` (false if either is NaN). -/
def le : F64 → F64 → Bool
  | .fin x, .fin y => decide ((x.ints y).1 ≤ (x.ints y).2)
  | .inf a, .inf b => a || !b
  | .inf a, .fin _ => a
  | .fin _, .inf b => !b
  | _, _ => false

def gt (x y : F64) : Bool := lt y x
def ge (x y : F64) : Bool := le y x

/-- Number::equal (`===` on numbers): NaN is unequal to everything, `+0 = -0`. -/
def eq : F64 → F64 → Bool
  | .fin x, .fin y => decide ((x.ints y).1 = (x.ints y).2)
  | .inf a, .inf b => a == b
  | _, _ => false

/-- SameValue (`Object.is`), which is Lean equality on `F64`. -/
def sameValue (x y : F64) : Bool := decide (x = y)

/-- SameValueZero: like `===` except that NaN equals NaN. -/
def sameValueZero (x y : F64) : Bool := (x.isNaN && y.isNaN) || eq x y

/-! ## Math functions -/

def floor : F64 → F64
  | .fin x =>
    if x.fracMag = 0 then .fin x
    else if x.neg then round true (x.intMag + 1) 0 else round false x.intMag 0
  | x => x

def ceil : F64 → F64
  | .fin x =>
    if x.fracMag = 0 then .fin x
    else if x.neg then round true x.intMag 0 else round false (x.intMag + 1) 0
  | x => x

def trunc : F64 → F64
  | .fin x => if x.fracMag = 0 then .fin x else round x.neg x.intMag 0
  | x => x

/-- `Math.round`: nearest integer, ties toward `+Infinity`; results in `[-0.5, -0]` are `-0`. -/
def jsRound : F64 → F64
  | .fin x =>
    if x.fracMag = 0 then .fin x
    else
      let up := if x.neg then decide (x.halfMag < x.fracMag) else decide (x.halfMag ≤ x.fracMag)
      round x.neg (if up then x.intMag + 1 else x.intMag) 0
  | x => x

/-- `Math.sign`. -/
def sign : F64 → F64
  | .nan => .nan
  | .inf b => if b then ofInt (-1) else one
  | .fin x => if x.man = 0 then .fin x else if x.neg then ofInt (-1) else one

/-- `Math.min` of two values: NaN wins, `-0 < +0`. -/
def min (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then .nan
  else if lt x y then x else if lt y x then y else if x.signBit then x else y

/-- `Math.max` of two values: NaN wins, `-0 < +0`. -/
def max (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then .nan
  else if lt x y then y else if lt y x then x else if x.signBit then y else x

/-- `y` is an odd integer. -/
def isOddInt (y : F64) : Bool :=
  match toInt? y with
  | some n => n % 2 != 0
  | none => false

/-- The results of Number::exponentiate (`x ** y`, `Math.pow`) that ECMA-262 §6.1.6.1.3 fixes
(steps 1-12): `none` exactly in the remaining case (step 13: `x` finite and non-zero, `y` finite
and non-zero, and `x > 0` or `y` an integer), where the result is implementation-approximated.
These differ from C's `pow` at `1 ** NaN`, `(±1) ** ±Infinity` (NaN in JavaScript). -/
def powSpec? (x y : F64) : Option F64 :=
  if y.isNaN then some nan
  else if y.isZero then some one
  else match x with
    | .nan => some nan
    | .inf false => some (if y.signBit then posZero else posInf)
    | .inf true =>
      some (if y.signBit then (if isOddInt y then negZero else posZero)
        else (if isOddInt y then negInf else posInf))
    | .fin a =>
      if a.man = 0 then
        if a.neg then
          some (if y.signBit then (if isOddInt y then negInf else posInf)
            else (if isOddInt y then negZero else posZero))
        else some (if y.signBit then posInf else posZero)
      else match y with
        | .inf neg =>
          if eq (abs x) one then some nan
          else some (if lt one (abs x) != neg then posInf else posZero)
        | _ => if a.neg && !isInteger y then some nan else none

/-- Number::exponentiate with `approx` (the host's power function) for the
implementation-approximated case: the specified results of `powSpec?` first. -/
def pow (approx : F64 → F64 → F64) (x y : F64) : F64 := (powSpec? x y).getD (approx x y)

/-! ## Integer conversions -/

/-- ToInt8/ToUint8/ToInt16/ToUint16/ToInt32/ToUint32 bits: truncate toward zero, modulo `2^n`;
NaN and `±Infinity` give `0`. -/
def toBitsN (n : Nat) (x : F64) : BitVec n := BitVec.ofInt n (truncInt x)

/-- ToInt32 / ToUint32 (both share these bits). -/
def toInt32 (x : F64) : BitVec 32 := toBitsN 32 x

/-- The Number with the signed value of `b`. -/
def ofIntN {n : Nat} (b : BitVec n) : F64 := ofInt b.toInt

/-- The Number with the unsigned value of `b`. -/
def ofUintN {n : Nat} (b : BitVec n) : F64 := ofInt b.toNat

def ofInt32 (b : BitVec 32) : F64 := ofInt b.toInt
def ofUint32 (b : BitVec 32) : F64 := ofInt b.toNat

/-- ToUint8Clamp (Uint8ClampedArray stores): clamp to `[0, 255]`, round half to even. -/
def toUint8Clamp : F64 → BitVec 8
  | .nan => 0
  | .inf b => if b then 0 else 255
  | .fin x =>
    if x.neg then 0
    else if 255 ≤ x.intMag then 255
    else
      let q := x.intMag
      let f := x.fracMag
      let up := f ≠ 0 && (decide (x.halfMag < f) || (decide (f = x.halfMag) && q % 2 == 1))
      BitVec.ofNat 8 (if up then q + 1 else q)

/-- `Math.clz32`. -/
def clz32 (x : F64) : F64 := ofNat (32 - bitLen (toInt32 x).toNat)

/-- `Math.imul`. -/
def imul (x y : F64) : F64 := ofInt32 (toInt32 x * toInt32 y)

/-! ## Bitwise operators (operands via ToInt32, shift counts via ToUint32 mod 32) -/

def band (x y : F64) : F64 := ofInt32 (toInt32 x &&& toInt32 y)
def bor (x y : F64) : F64 := ofInt32 (toInt32 x ||| toInt32 y)
def bxor (x y : F64) : F64 := ofInt32 (toInt32 x ^^^ toInt32 y)
def bnot (x : F64) : F64 := ofInt32 (~~~toInt32 x)
/-- `x << y`. -/
def shl (x y : F64) : F64 := ofInt32 (toInt32 x <<< ((toInt32 y).toNat % 32))
/-- `x >> y` (sign-propagating). -/
def sar (x y : F64) : F64 := ofInt32 ((toInt32 x).sshiftRight ((toInt32 y).toNat % 32))
/-- `x >>> y` (zero-fill; the result is unsigned). -/
def shr (x y : F64) : F64 := ofUint32 (toInt32 x >>> ((toInt32 y).toNat % 32))

/-! ## Bit patterns -/

/-- IEEE-754 binary64 encoding; NaN is encoded as the canonical `0x7FF8000000000000`. -/
def toBits : F64 → BitVec 64
  | .nan => 0x7FF8000000000000#64
  | .inf b => BitVec.ofNat 64 ((if b then 2^63 else 0) + 2047 * 2^52)
  | .fin x =>
    let s := if x.neg then 2^63 else 0
    if x.man < 2^52 then BitVec.ofNat 64 (s + x.man)
    else BitVec.ofNat 64 (s + (x.exp + 1075).toNat * 2^52 + (x.man - 2^52))

/-- Decoding of binary64 bit patterns; every NaN pattern gives `nan`. -/
def ofBits (b : BitVec 64) : F64 :=
  let n := b.toNat
  let neg := decide (2^63 ≤ n)
  let be := (n >>> 52) % 2048
  let f := n % 2^52
  if be = 2047 then (if f = 0 then .inf neg else .nan)
  else if be = 0 then mkFin neg f (-1074)
  else mkFin neg (f + 2^52) ((be : Int) - 1075)

/-- Binary32 encoding of `(-1)^neg * m * 2^e`, round-half-even with subnormals and overflow. -/
def roundF32Bits (neg : Bool) (m : Nat) (e : Int) : BitVec 32 :=
  let s32 : Nat := if neg then 2^31 else 0
  if m = 0 then BitVec.ofNat 32 s32
  else
    let E : Int := e + (bitLen m : Int) - 1
    let q : Int := if E - 23 ≤ -149 then -149 else E - 23
    let man1 : Nat :=
      if q ≤ e then m <<< (e - q).toNat
      else
        let s : Nat := (q - e).toNat
        let man0 := m >>> s
        let rem := m - (man0 <<< s)
        let half := 1 <<< (s - 1)
        if half < rem || (rem = half && man0 % 2 == 1) then man0 + 1 else man0
    let man := if man1 = 2^24 then 2^23 else man1
    let q2 := if man1 = 2^24 then q + 1 else q
    if q2 > 104 then BitVec.ofNat 32 (s32 + 0x7F800000)
    else if man < 2^23 then BitVec.ofNat 32 (s32 + man)
    else BitVec.ofNat 32 (s32 + (q2 + 150).toNat * 2^23 + (man - 2^23))

/-- Nearest binary32 encoding (round-half-even); NaN gives `0x7FC00000`. -/
def toF32Bits : F64 → BitVec 32
  | .nan => 0x7FC00000#32
  | .inf b => if b then 0xFF800000#32 else 0x7F800000#32
  | .fin x => roundF32Bits x.neg x.man x.exp

/-- Exact widening of a binary32 bit pattern; every NaN pattern gives `nan`. -/
def ofF32Bits (b : BitVec 32) : F64 :=
  let n := b.toNat
  let neg := decide (2^31 ≤ n)
  let be := (n >>> 23) % 256
  let f := n % 2^23
  if be = 255 then (if f = 0 then .inf neg else .nan)
  else if be = 0 then round neg f (-149)
  else round neg (f + 2^23) ((be : Int) - 150)

/-- `Math.fround`. -/
def fround (x : F64) : F64 := ofF32Bits (toF32Bits x)

/-- Zero-padded hexadecimal digits. -/
def hexPad (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) '0') ++ s

instance : Repr F64 where
  reprPrec x _ := match x with
    | .nan => "F64.nan"
    | .inf false => "F64.posInf"
    | .inf true => "F64.negInf"
    | .fin _ => "F64.ofBits 0x" ++ hexPad (toBits x).toNat 16 ++ "#64"

end F64

/-! ## Small examples checked by `decide` -/

section Examples
open F64

example : ofInt 1 + ofInt 2 = ofInt 3 := by decide
example : (ofInt 7).toInt32 = 7#32 := by decide
example : ofInt 6 * ofInt 7 = ofInt 42 := by decide
example : ofInt 0 * ofInt (-3) = negZero := by decide
example : ofInt 3 - ofInt 3 = posZero := by decide
example : negZero + negZero = negZero := by decide
example : posZero + negZero = posZero := by decide
example : (ofInt 7 / ofInt 2).floor = ofInt 3 := by decide
example : ofInt 5 % ofInt (-3) = ofInt 2 := by decide
example : ofInt (-5) % ofInt 3 = ofInt (-2) := by decide
example : sqrt (ofInt 9) = ofInt 3 := by decide
example : ofInt 1 / ofInt 0 = posInf := by decide
example : (ofInt 0 / ofInt 0).isNaN = true := by decide
example : (ofInt (-1)).toInt32 = 0xFFFFFFFF#32 := by decide
example : (ofInt 3).toBits = 0x4008000000000000#64 := by decide
example : ofBits 0x4008000000000000#64 = ofInt 3 := by decide
example : (ofInt 3).lt (ofInt 4) = true := by decide
example : jsRound (ofInt (-5) / ofInt 2) = ofInt (-2) := by decide
example : jsRound (ofInt (-1) / ofInt 2) = negZero := by decide
example : imul (ofInt 3) (ofInt (-4)) = ofInt (-12) := by decide
example : shr (ofInt (-1)) (ofInt 0) = ofInt 4294967295 := by decide
example : (ofInt 1 / ofInt 10 + ofInt 2 / ofInt 10).eq (ofInt 3 / ofInt 10) = false := by decide
example : (ofInt 1 / ofInt 10 + ofInt 2 / ofInt 10).toBits = 0x3FD3333333333334#64 := by decide
example : fround (ofInt 1 / ofInt 3) = ofBits 0x3FD5555560000000#64 := by decide
example : maxValue.toBits = 0x7FEFFFFFFFFFFFFF#64 := by decide
example : minValue.toBits = 0x0000000000000001#64 := by decide
example : epsilon.toBits = 0x3CB0000000000000#64 := by decide
example : maxSafeInteger.toBits = 0x433FFFFFFFFFFFFF#64 := by decide
example : minSafeInteger.toBits = 0xC33FFFFFFFFFFFFF#64 := by decide
example : one.toBits = 0x3FF0000000000000#64 := by decide
example : (maxSafeInteger + one).isSafeInteger = false := by decide

end Examples

end StrictTS
