import CIR.Std.Float

/-!
  Correctly rounded `erf`, `erfc`, `tgamma` and `lgamma`. glibc 2.43 computes these four functions
  with the CORE-MATH project's correctly rounded code: the result is the double nearest to the exact
  value, so any correct rounding of the exact value gives glibc's bits, whatever the algorithm.
  The exact value is enclosed in an interval with dyadic endpoints (`Iv`), from series whose
  remainders are bounded rigorously, at a working precision that doubles until both endpoints round
  to the same double (Ziv's strategy). Exact cases whose value could be a tie (`tgamma` of an
  integer) are rounded from the exact value; past 2048 bits the rounding is left undecided
  (`none`), which no double argument is known to need.
-/

namespace CIR.Std.CR

/-- The number of bits of `|n|` (0 for 0). -/
def bitlen (n : Int) : Nat := if n = 0 then 0 else Nat.log2 n.natAbs + 1

/-- `⌊a / b⌋` and `⌈a / b⌉` for `b > 0`. -/
def divFloor (a : Int) (b : Nat) : Int := Int.fdiv a b
def divCeil (a : Int) (b : Nat) : Int := -Int.fdiv (-a) b

/-- The interval `[lo · 2^e, hi · 2^e]` (`lo ≤ hi`). -/
structure Iv where
  lo : Int
  hi : Int
  e : Int
  deriving Inhabited

namespace Iv

def ofInt (n : Int) : Iv := ⟨n, n, 0⟩

/-- The point `m · 2^e`. -/
def pt (m e : Int) : Iv := ⟨m, m, e⟩

def isZero (x : Iv) : Bool := x.lo == 0 && x.hi == 0

/-- The bits of the larger endpoint magnitude. -/
def mag (x : Iv) : Nat := max (bitlen x.lo) (bitlen x.hi)

/-- Every value of `x` is below `2^x.top` in magnitude. -/
def top (x : Iv) : Int := (x.mag : Int) + x.e

/-- Rounded outward to at most `p` bits per endpoint. -/
def trim (p : Nat) (x : Iv) : Iv :=
  if x.mag ≤ p then x else
  let k := x.mag - p
  ⟨x.lo >>> k, -((-x.hi) >>> k), x.e + k⟩

/-- The same interval written with at least `p` bits. -/
def widen (p : Nat) (x : Iv) : Iv :=
  if p ≤ x.mag then x else
  let k := p - x.mag
  ⟨x.lo * 2 ^ k, x.hi * 2 ^ k, x.e - k⟩

def neg (x : Iv) : Iv := ⟨-x.hi, -x.lo, x.e⟩

/-- `x · 2^k`. -/
def scale (x : Iv) (k : Int) : Iv := ⟨x.lo, x.hi, x.e + k⟩

/-- `x + y` at precision `p`: an addend entirely below the other's last place counts as one
unit of that place, of its sign. -/
def add (p : Nat) (x y : Iv) : Iv :=
  let x := widen (p + 2) x
  let y := widen (p + 2) y
  if y.top ≤ x.e then
    trim p ⟨x.lo - (if y.lo < 0 then 1 else 0), x.hi + (if 0 < y.hi then 1 else 0), x.e⟩
  else if x.top ≤ y.e then
    trim p ⟨y.lo - (if x.lo < 0 then 1 else 0), y.hi + (if 0 < x.hi then 1 else 0), y.e⟩
  else
    let e := min x.e y.e
    let sx := (x.e - e).toNat
    let sy := (y.e - e).toNat
    trim p ⟨x.lo * 2 ^ sx + y.lo * 2 ^ sy, x.hi * 2 ^ sx + y.hi * 2 ^ sy, e⟩

def sub (p : Nat) (x y : Iv) : Iv := add p x (neg y)

def mul (p : Nat) (x y : Iv) : Iv :=
  let a := x.lo * y.lo
  let b := x.lo * y.hi
  let c := x.hi * y.lo
  let d := x.hi * y.hi
  trim p ⟨min (min a b) (min c d), max (max a b) (max c d), x.e + y.e⟩

/-- `x / n` for a positive integer `n`. -/
def divNat (p : Nat) (x : Iv) (n : Nat) : Iv :=
  let x := widen (p + bitlen n + 2) x
  trim p ⟨divFloor x.lo n, divCeil x.hi n, x.e⟩

/-- `1 / x` for a positive `x`. -/
def invPos (p : Nat) (x : Iv) : Iv :=
  let s := p + x.mag + 4
  trim p ⟨divFloor (2 ^ s) x.hi.toNat, divCeil (2 ^ s) x.lo.toNat, -(s : Int) - x.e⟩

/-- An interval too wide to round: what an evaluation outside its domain gives. -/
def wide : Iv := ⟨-1, 1, 4096⟩

/-- `1 / x` for `x` not containing 0. -/
def inv (p : Nat) (x : Iv) : Iv :=
  if 0 < x.lo then invPos p x
  else if x.hi < 0 then neg (invPos p (neg x))
  else wide

def div (p : Nat) (x y : Iv) : Iv := mul p x (inv (p + 4) y)

/-- `√x` for `x ≥ 0`. -/
def sqrt (p : Nat) (x : Iv) : Iv :=
  if x.lo < 0 then wide else
  let x := widen (2 * p + 4) x
  let x := if x.e % 2 = 0 then x else ⟨x.lo * 2, x.hi * 2, x.e - 1⟩
  let s := Nat.sqrt x.hi.toNat
  trim p ⟨Nat.sqrt x.lo.toNat, if s * s = x.hi.toNat then s else s + 1, x.e / 2⟩

/-- The smallest interval containing the lower end of `x` and the upper end of `y`. -/
def hull (x y : Iv) : Iv :=
  let e := min x.e y.e
  ⟨x.lo * 2 ^ (x.e - e).toNat, y.hi * 2 ^ (y.e - e).toNat, e⟩

/-- The double nearest to `m · 2^e` (ties to even; infinite beyond the largest double). -/
def dyToFloat (m e : Int) : Float :=
  if m = 0 then 0.0 else
  let t := (bitlen m : Int) + e
  if 1026 < t then infF (decide (m < 0))
  else if t < -1076 then (if m < 0 then -0.0 else 0.0)
  else valToFloat (decide (m < 0)) m.natAbs e

/-- The double every value of `x` rounds to, if there is one. -/
def round (x : Iv) : Option Float :=
  let a := dyToFloat x.lo x.e
  let b := dyToFloat x.hi x.e
  if a.toBits == b.toBits then some a else none

end Iv

open Iv

/-- Ziv's strategy: `f p` encloses the value at working precision `p`; 128 bits first, doubled
up to 2048 bits. -/
def ziv (f : Nat → Iv) : Option Float :=
  let rec go (p : Nat) : Nat → Option Float
    | 0 => none
    | fuel + 1 => match (f p).round with
      | some r => some r
      | none => go (2 * p) fuel
  go 128 5

/-! ### Constants -/

/-- `atan (1/n) · 2^P` within `err`, as `(s, err)`: the alternating series, each term `⌊2^P /
((2k+1) n^(2k+1))⌋` exactly (a floor of floors), up to the first zero term. -/
def atanInvFix (n P : Nat) : Int × Nat :=
  let rec go (pow k : Nat) (s : Int) : Nat → Int × Nat
    | 0 => (s, k + 2)
    | fuel + 1 =>
      let t := pow / (2 * k + 1)
      if t = 0 then (s, k + 1)
      else go (pow / (n * n)) (k + 1) (if k % 2 = 0 then s + t else s - t) fuel
  go (2 ^ P / n) 0 0 (P + 2)

/-- `π` by Machin's formula, `16 atan (1/5) - 4 atan (1/239)`, at `P` fractional bits. -/
def piFix (P : Nat) : Iv :=
  let (a, ea) := atanInvFix 5 P
  let (b, eb) := atanInvFix 239 P
  let c := 16 * a - 4 * b
  let err : Int := 16 * ea + 4 * eb
  ⟨c - err, c + err, -(P : Int)⟩

/-- `ln 2 = 2 atanh (1/3) = Σ 2 / ((2k+1) 3^(2k+1))` at `P` fractional bits (positive terms: the
tail past a zero term is below `9/8`). -/
def ln2Fix (P : Nat) : Iv :=
  let rec go (pow k s : Nat) : Nat → Nat × Nat
    | 0 => (s, k + 3)
    | fuel + 1 =>
      let t := pow / (2 * k + 1)
      if t = 0 then (s, k + 2) else go (pow / 9) (k + 1) (s + t) fuel
  let (s, err) := go (2 ^ P / 3) 0 0 (P + 2)
  ⟨2 * ((s : Int) - err), 2 * ((s : Int) + err), -(P : Int)⟩

def piCache : Thunk Iv := Thunk.mk fun _ => piFix 2304
def ln2Cache : Thunk Iv := Thunk.mk fun _ => ln2Fix 2304

def piIv (p : Nat) : Iv := if p ≤ 2240 then trim p piCache.get else trim p (piFix (p + 16))
def ln2Iv (p : Nat) : Iv := if p ≤ 2240 then trim p ln2Cache.get else trim p (ln2Fix (p + 16))

/-! ### Elementary functions -/

/-- `e^d` for `|d| ≤ 2^-8` by Taylor's series, up to a term below `2^-(p+4)`; the rest is below
twice that term. -/
def expSeries (p : Nat) (d : Iv) : Iv :=
  let rec go (t s : Iv) (j : Nat) : Nat → Iv
    | 0 => wide
    | fuel + 1 =>
      let t := divNat p (mul p t d) j
      if t.isZero then s
      else if t.top < -(p : Int) - 4 then add p s ⟨-1, 1, t.top + 1⟩
      else go t (add p s t) (j + 1) fuel
  go (ofInt 1) (ofInt 1) 1 (p + 16)

/-- An integer near `v / ln 2` for `v` in `x` (any integer is correct; a near one is fast). -/
def nearLog2e (x : Iv) : Int :=
  -- `0x171547652B82FE · 2^-52` is `1/ln 2` to 53 bits
  let a := x.lo * 0x171547652B82FE
  let s := x.e - 52
  if 0 ≤ s then a * 2 ^ s.toNat else (a + 2 ^ ((-s).toNat - 1)) >>> (-s).toNat

/-- `e^v` for `v` in `x` (`|x|` below about `2^20`): `v = k ln 2 + r`, `e^r = (e^(r/256))^256`. -/
def expIv (p : Nat) (x : Iv) : Iv :=
  if 24 < x.top then wide else
  let q := p + 24
  let k := nearLog2e x
  let r := sub q x (mul q (ofInt k) (ln2Iv (q + bitlen k + 8)))
  let rec sq (y : Iv) : Nat → Iv
    | 0 => y
    | n + 1 => sq (mul q y y) n
  -- each endpoint separately: `exp` is increasing
  let lo := sq (expSeries q (scale (pt r.lo r.e) (-8))) 8
  let hi := sq (expSeries q (scale (pt r.hi r.e) (-8))) 8
  trim p (scale (hull lo hi) k)

/-- `atanh t = Σ t^(2k+1) / (2k+1)` for `|t| ≤ 1/5`, up to a term below `2^-(p+4)` of the sum; the
rest is below twice that term. -/
def atanhSeries (p : Nat) (t : Iv) : Iv :=
  let t2 := mul p t t
  let rec go (pw s : Iv) (k : Nat) : Nat → Iv
    | 0 => wide
    | fuel + 1 =>
      let pw := mul p pw t2
      let term := divNat p pw (2 * k + 1)
      if term.isZero then s
      else if term.top < s.top - p - 4 then add p s ⟨-1, 1, term.top + 1⟩
      else go pw (add p s term) (k + 1) fuel
  if t.isZero then t else go t t 1 (p + 16)

/-- `ln (m · 2^e)` for `m > 0`: `m · 2^e = f · 2^E` with `3/4 ≤ f < 3/2`, `ln f = 2 atanh ((f -
1) / (f + 1))`. -/
def logPoint (p : Nat) (m : Nat) (e : Int) : Iv :=
  let q := p + 12
  let L := Nat.log2 m
  let big := 3 * 2 ^ L ≤ 2 * m
  let E : Int := (L : Int) + e + (if big then 1 else 0)
  let den : Nat := if big then 2 ^ (L + 1) else 2 ^ L
  let t := div q (ofInt ((m : Int) - den)) (ofInt (m + den))
  let lnf := scale (atanhSeries q t) 1
  if E = 0 then trim p lnf
  else trim p (add q (mul q (ofInt E) (ln2Iv (q + bitlen E + 4))) lnf)

/-- `ln v` for `v` in the positive interval `x`. -/
def logIv (p : Nat) (x : Iv) : Iv :=
  if x.lo ≤ 0 then wide
  else hull (logPoint p x.lo.toNat x.e) (logPoint p x.hi.toNat x.e)

/-- `sin y` for `|y| ≤ π/2`: the alternating series, its terms decreasing, up to a term below
`2^-(p+4)` of the sum, which bounds the rest. -/
def sinSeries (p : Nat) (y : Iv) : Iv :=
  let y2 := mul p y y
  let rec go (t s : Iv) (j : Nat) : Nat → Iv
    | 0 => wide
    | fuel + 1 =>
      let t := neg (divNat p (mul p t y2) (2 * j * (2 * j + 1)))
      if t.isZero then s
      else if t.top < s.top - p - 4 then add p s ⟨-1, 1, t.top⟩
      else go t (add p s t) (j + 1) fuel
  if y.isZero then y else go y y 1 (p + 16)

/-- `sin (π f)` for `0 < f ≤ 1/2`. -/
def sinPi (p : Nat) (f : Iv) : Iv := trim p (sinSeries (p + 8) (mul (p + 8) (piIv (p + 8)) f))

/-! ### erf, erfc -/

/-- `Σ (-1)^n x^(2n+1) / (n! (2n+1))` (`erf x · √π / 2`) for an exact `x > 0`, at precision `q`
relative to the largest term, up to a term below `2^stop` once the terms decrease
(`n ≥ x²`): an alternating series, its rest below that term. -/
def erfSum (q : Nat) (stop : Int) (x : Iv) (x2c : Nat) : Iv :=
  let x2 := mul q x x
  let rec go (t s : Iv) (n : Nat) : Nat → Iv
    | 0 => wide
    | fuel + 1 =>
      let t := divNat q (mul q t x2) n
      let u := divNat q t (2 * n + 1)
      let u := if n % 2 = 1 then neg u else u
      if x2c ≤ n && u.top < stop then add q s ⟨-1, 1, u.top⟩
      else go t (add q s u) (n + 1) fuel
  go x x 1 (4 * x2c + q + 64)

/-- `2 / √π`. -/
def twoOverSqrtPi (p : Nat) : Iv := div p (ofInt 2) (sqrt (p + 4) (piIv (p + 8)))

/-- `⌈x²⌉` for the exact positive `x = m · 2^e`. -/
def sqCeil (m : Nat) (e : Int) : Nat :=
  if 0 ≤ e then m * m * 4 ^ e.toNat else (m * m + 4 ^ (-e).toNat - 1) / 4 ^ (-e).toNat

/-- `erf x` for the exact `x = m · 2^e > 0`, at working precision `p`. -/
def erfIv (p : Nat) (m : Nat) (e : Int) : Iv :=
  let x := pt m e
  let x2c := sqCeil m e
  -- the largest term is below `2^(1.5 x²)` (`e^(x²)`); the result is near `min (x, 1)`
  let res : Int := min (x.top - 1) 0
  let q := p + 24 + 3 * x2c / 2
  trim p (mul q (twoOverSqrtPi q) (erfSum q (res - p - 8) x x2c))

/-- `erfc x = 1 - erf x` for the exact `x = m · 2^e > 0`: the result is near `e^(-x²) / (x √π)`,
below `2^(1 - 1.44 x²)`, so the series runs at that many bits more below 1. -/
def erfcIv (p : Nat) (m : Nat) (e : Int) : Iv :=
  let x := pt m e
  let x2c := sqCeil m e
  -- `erfc x > e^(-x²) / (√π (x + 1))` for `x > 0`, above `2^(-1.45 x² - 1 - log₂ (x + 1))`
  let res : Int := -((145 * x2c / 100 + 1 : Nat) : Int) - max x.top 0 - 2
  let q := p + 40 + 3 * x2c + (max x.top 0).toNat
  let s := mul q (twoOverSqrtPi q) (erfSum q (res - p - 8) x x2c)
  trim p (sub q (ofInt 1) s)

/-! ### Γ and ln Γ -/

/-- The tangent numbers `T_1 … T_n` (Brent and Harvey's recurrence; index 0 unused):
`B_2k = (-1)^(k-1) 2k T_k / (4^k (4^k - 1))`. -/
def tangentNumbers (n : Nat) : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate (n + 1) 0
  t := t.set! 1 1
  for k in [2:n+1] do
    t := t.set! k ((k - 1) * t[k-1]!)
  for k in [2:n+1] do
    for j in [k:n+1] do
      t := t.set! j ((j - k) * t[j-1]! + (j - k + 2) * t[j]!)
  return t

def tangentCache : Thunk (Array Nat) := Thunk.mk fun _ => tangentNumbers 256

/-- `ln Γ(z)` for an exact `z ≥ 16`, within `2^-p` absolutely: Stirling's series `(z - 1/2) ln z -
z + ln (2π) / 2 + Σ B_2k / (2k (2k-1) z^(2k-1))`, up to a term below `2^-(p+4)`; for real `z > 0`
the rest is below the first term left out. -/
def lnGammaStirling (p : Nat) (z : Iv) : Iv :=
  -- `(z - 1/2) ln z - z` is below `2^(z.top + bitlen z.top)`: that many more bits
  let q := p + 24 + (max z.top 0).toNat + bitlen z.top
  let main := sub q (mul q (sub q z ⟨1, 1, -1⟩) (logIv q z)) z
  let base := add q main (scale (logIv q (scale (piIv q) 1)) (-1))
  let zi := inv q z
  let zi2 := mul q zi zi
  let T := tangentCache.get
  let rec go (k : Nat) (pw s : Iv) : Nat → Iv
    | 0 => wide
    | fuel + 1 =>
      if T.size ≤ k then wide else
      let u := divNat q (mul q pw (ofInt T[k]!)) (4 ^ k * (4 ^ k - 1) * (2 * k - 1))
      let u := if k % 2 = 1 then u else neg u
      if u.top < -(p : Int) - 4 then add q s ⟨-1, 1, u.top⟩
      else go (k + 1) (mul q pw zi2) (add q s u) fuel
  go 1 zi base 300

/-- The exact sum `x + n`. -/
def addNat (x : Iv) (n : Nat) : Iv :=
  if 0 ≤ x.e then ⟨x.lo * 2 ^ x.e.toNat + n, x.hi * 2 ^ x.e.toNat + n, 0⟩
  else ⟨x.lo + n * 2 ^ (-x.e).toNat, x.hi + n * 2 ^ (-x.e).toNat, x.e⟩

/-- The shift that brings `x > 0` to at least `16 + p/2` (where Stirling's series reaches
`2^-p` within 256 terms), and `x (x+1) … (x+n-1)`. -/
def shiftUp (p : Nat) (x : Iv) : Nat × Iv :=
  let zmin : Nat := 16 + p / 2
  -- `⌊x⌋` (x exact and positive)
  let fl : Nat := (if 0 ≤ x.e then x.lo * 2 ^ x.e.toNat else x.lo >>> (-x.e).toNat).toNat
  let n := zmin - fl
  let q := p + 16
  let rec prod (j : Nat) (acc : Iv) : Nat → Iv
    | 0 => acc
    | k + 1 => prod (j + 1) (mul q acc (addNat x j)) k
  (n, prod 0 (ofInt 1) n)

/-- `ln Γ(x)` for an exact `x > 0`, within `2^-p` absolutely (relatively when `x` is near 1 or 2
only as `p` allows: Ziv's loop raises it). -/
def lnGammaPos (p : Nat) (x : Iv) : Iv :=
  let (n, P) := shiftUp p x
  let q := p + 8
  sub q (lnGammaStirling q (addNat x n)) (logIv q P)

/-- `Γ(x)` for an exact `x > 0`, at relative precision about `p`. -/
def gammaPos (p : Nat) (x : Iv) : Iv :=
  let (n, P) := shiftUp p x
  let q := p + 16
  let lg := lnGammaStirling (q + 16) (addNat x n)
  trim p (div q (expIv q lg) P)

/-- `x mod 2` in `[0, 2)` for an exact `x` with a negative exponent. -/
def mod2 (x : Iv) : Iv := ⟨x.lo % 2 ^ (1 - x.e).toNat, x.lo % 2 ^ (1 - x.e).toNat, x.e⟩

/-- `|sin (π x)|` and the sign of `sin (π x)` for an exact non-integer `x` with a negative exponent:
from `f = x mod 2`, `sin (π g)` for `g = min (f, 1 - f)` or `min (f - 1, 2 - f)` in `(0, 1/2]`. -/
def sinPiAbs (p : Nat) (x : Iv) : Iv × Bool :=
  let f := mod2 x
  let one : Int := 2 ^ (-x.e).toNat
  let (g, neg) := if f.lo < one then (min f.lo (one - f.lo), false)
    else (min (f.lo - one) (2 * one - f.lo), true)
  (sinPi p (pt g x.e), neg)

/-- `Γ(x)` for an exact negative non-integer `x`: `π / (sin (π x) Γ(1 - x))`. -/
def gammaNeg (p : Nat) (x : Iv) : Iv :=
  let q := p + 16
  let (s, neg) := sinPiAbs q x
  let g := div q (piIv q) (mul q s (gammaPos q (addNat (Iv.neg x) 1)))
  trim p (if neg then Iv.neg g else g)

/-- `ln |Γ(x)|` for an exact negative non-integer `x`: `ln π - ln |sin (π x)| - ln Γ(1 - x)`. -/
def lnGammaNeg (p : Nat) (x : Iv) : Iv :=
  let q := p + 16
  let (s, _) := sinPiAbs q x
  trim p (sub q (sub q (logIv q (piIv q)) (logIv q s)) (lnGammaPos q (addNat (Iv.neg x) 1)))

/-! ### The functions -/

/-- `n!` -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The exact value `±m · 2^e`. -/
def ptOf (neg : Bool) (m : Nat) (e : Int) : Iv := pt (if neg then -(m : Int) else m) e

/-- Whether `m · 2^e` is an integer. -/
def isInt (m : Nat) (e : Int) : Bool := 0 ≤ e || m % 2 ^ (-e).toNat == 0

/-- `m · 2^e ≥ c`, exactly. -/
def geNat (m : Nat) (e : Int) (c : Nat) : Bool :=
  if 0 ≤ e then c ≤ m * 2 ^ e.toNat else c * 2 ^ (-e).toNat ≤ m

/-- `⌊m · 2^e⌋`. -/
def floorOf (m : Nat) (e : Int) : Nat := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat

/-- Correctly rounded `erf x`. -/
def erfCR (x : Float) : Option Float :=
  match decodeF x with
  | .nan => some x
  | .inf neg => some (if neg then -1.0 else 1.0)
  | .finite neg m e =>
    if m = 0 then some x
    -- `erfc 6 < e^-36 / (6 √π) < 2^-54`: from 6 on, `erf` rounds to 1
    else if geNat m e 6 then some (if neg then -1.0 else 1.0)
    else (ziv fun p => erfIv p m e).map fun r => if neg then -r else r

/-- Correctly rounded `erfc x`. -/
def erfcCR (x : Float) : Option Float :=
  match decodeF x with
  | .nan => some x
  | .inf neg => some (if neg then 2.0 else 0.0)
  | .finite neg m e =>
    if m = 0 then some 1.0
    else if neg then
      -- `1 + erf |x|`; `erfc 6 < 2^-53`: from 6 on, the result rounds to 2
      if geNat m e 6 then some 2.0 else ziv fun p => add p (ofInt 1) (erfIv (p + 4) m e)
    -- `erfc 28 < e^-784 < 2^-1075`: from 28 on, the result rounds to +0
    else if geNat m e 28 then some 0.0
    else ziv fun p => erfcIv p m e

/-- Correctly rounded `tgamma x`. -/
def tgammaCR (x : Float) : Option Float :=
  match decodeF x with
  | .nan => some x
  | .inf neg => some (if neg then nanF else x)
  | .finite neg m e =>
    if m = 0 then some (infF neg)
    else if isInt m e then
      if neg then some nanF
      -- `Γ(172) = 171!` exceeds the largest double
      else if geNat m e 172 then some (infF false)
      else some (Iv.dyToFloat (fact (floorOf m e - 1)) 0)
    else if neg then
      -- below -200, `|Γ(x)| ≤ π / (2^-44 · 200!) < 2^-1075` (`|sin (π x)| ≥ 2^-44` there): a
      -- zero of the sign of `Γ(x)`, `-` when `⌊x⌋` is odd
      if geNat m e 200 then some (if (floorOf m e + 1) % 2 = 1 then -0.0 else 0.0)
      else ziv fun p => gammaNeg p (ptOf true m e)
    -- `Γ` increases from 2 on: from 172, past the largest double
    else if geNat m e 172 then some (infF false)
    else ziv fun p => gammaPos p (ptOf false m e)

/-- Correctly rounded `lgamma x` (the sign glibc stores in `signgam` is `lgammaSign x`). -/
def lgammaCR (x : Float) : Option Float :=
  match decodeF x with
  | .nan => some x
  | .inf _ => some (infF false)
  | .finite neg m e =>
    if m = 0 then some (infF false)
    else if isInt m e && neg then some (infF false)
    else if isInt m e && !geNat m e 3 then some 0.0
    -- from `2^1016` on, `ln Γ(x) > x (ln x - 1)` exceeds the largest double
    else if geNat m e (2 ^ 1016) then some (infF false)
    else if isInt m e && !geNat m e 200 then
      ziv fun p => logIv p (ofInt (fact (floorOf m e - 1)))
    else if neg then ziv fun p => lnGammaNeg p (ptOf true m e)
    else ziv fun p => lnGammaPos p (ptOf false m e)

/-- The sign that glibc's `lgamma` stores in `signgam` (its `__ieee754_lgamma_r`): -1 where `Γ(x)`
is negative, that is at a negative zero and at a negative non-integer whose floor is odd (the floor
of `|x|` even); 1 elsewhere, NaN, the infinities and the poles included. -/
def lgammaSign (x : Float) : Int :=
  match decodeF x with
  | .finite true m e =>
    if m = 0 then -1
    else if isInt m e then 1
    else if floorOf m e % 2 = 0 then -1 else 1
  | _ => 1

end CIR.Std.CR
