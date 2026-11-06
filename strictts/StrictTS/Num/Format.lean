/-
StrictTS: exact Number and BigInt to String conversions (ECMA-262 §6.1.6.1.20, §21.1.3).

All digit generation is exact integer arithmetic on the binary value `man * 2^exp` of a double;
no floating-point arithmetic is used except where V8's own double arithmetic is reproduced
(`v8RadixInt`). Outputs agree with Node/V8 (see `tests/StrDiff.lean`).
-/
import StrictTS.Num.F64
import StrictTS.Str.JSStr

namespace StrictTS
namespace NumFormat

open F64 (bitLen)

/-! ## Digits -/

/-- ASCII digit `0-9a-z` for a digit value below 36. -/
def digitUnit (d : Nat) : UInt16 := if d < 10 then (48 + d).toUInt16 else (87 + d).toUInt16

/-- Digits of `n` in base `b`, most significant first, prepended to `acc`
(same recursion as `Nat.toDigitsCore`). -/
def digitsCore (b : Nat) : Nat → Nat → List UInt16 → List UInt16
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := digitUnit (n % b)
    let n' := n / b
    if n' = 0 then d :: acc else digitsCore b fuel n' (d :: acc)

/-- Digits of `n` in base `b ≥ 2` (`"0"` for `0`). -/
def natDigits (b n : Nat) : List UInt16 := digitsCore b (n + 1) n []

/-! ## Exact helpers on `m * 2^e` -/

/-- `some v` when `m * 2^e` is the integer `v`. -/
def intValue? (m : Nat) (e : Int) : Option Nat :=
  if 0 ≤ e then some (m * 2 ^ e.toNat)
  else if m % 2 ^ (-e).toNat = 0 then some (m / 2 ^ (-e).toNat) else none

/-- `N * 2^eb / r^j` as a fraction `(num, den)`. -/
def scaled (r N : Nat) (eb j : Int) : Nat × Nat :=
  (N * 2 ^ eb.toNat * r ^ (-j).toNat, 2 ^ (-eb).toNat * r ^ j.toNat)

/-- `10^d ≤ m * 2^e`. -/
def pow10Le (m : Nat) (e d : Int) : Bool :=
  decide (10 ^ d.toNat * 2 ^ (-e).toNat ≤ m * 2 ^ e.toNat * 10 ^ (-d).toNat)

/-- Largest `j` in `[lo, hi)` satisfying the monotone (true-then-false) predicate `p`,
given `p lo`; `fuel` bounds the bisection steps. -/
def searchMax (p : Int → Bool) : Nat → Int → Int → Int
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := lo + (hi - lo) / 2
      if p mid then searchMax p fuel mid hi else searchMax p fuel lo mid

/-- Estimate `d` of `⌊log₁₀ (m * 2^e)⌋` for a double `m * 2^e > 0`: the true value lies in
`[d - 1, d + 2]` (`78913 / 2^18` is `log₁₀ 2` to within `3 * 10^-8`, and `|e + bitLen m| ≤ 1100`). -/
def log10Estimate (m : Nat) (e : Int) : Int := ((e + bitLen m - 1) * 78913) / 262144

/-- `⌊log₁₀ (m * 2^e)⌋` for `m > 0`. -/
def log10Floor (m : Nat) (e : Int) : Int :=
  let d := log10Estimate m e
  searchMax (pow10Le m e) 6 (d - 3) (d + 4)

/-- Nearest natural number to `num / den`, ties to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if den < 2 * r then q + 1 else if 2 * r < den then q else if q % 2 = 0 then q else q + 1

/-- Nearest natural number to `num / den`, ties up. -/
def roundHalfUp (num den : Nat) : Nat := (2 * num + den) / (2 * den)

/-- `m * 2^e * 10^p` rounded half up. -/
def scaledRound (m : Nat) (e p : Int) : Nat :=
  roundHalfUp (m * 2 ^ e.toNat * 10 ^ p.toNat) (2 ^ (-e).toNat * 10 ^ (-p).toNat)

/-! ## Shortest round-trip digits -/

/-- Rounding interval of the positive double `m * 2^e` in units of `2^(e-2)`: every real in it
rounds (to nearest, ties to even) to the double. The ends belong to it iff `m` is even. The
interval is asymmetric below a power of two whose predecessor has a smaller quantum. -/
structure Interval where
  lowN : Nat
  highN : Nat
  eb : Int
  incl : Bool

/-- The rounding interval of `m * 2^e`, `m > 0`. -/
def interval (m : Nat) (e : Int) : Interval :=
  let asym := m == 2 ^ 52 && decide (-1074 < e)
  { lowN := if asym then 4 * m - 1 else 4 * m - 2, highN := 4 * m + 2, eb := e - 2,
    incl := m % 2 == 0 }

/-- The range `[cmin, cmax]` of integers `c` with `c * r^j` in the interval `I`. -/
def candidates (r : Nat) (I : Interval) (j : Int) : Nat × Nat :=
  let (nl, den) := scaled r I.lowN I.eb j
  let nh := (scaled r I.highN I.eb j).1
  let cmin := if I.incl then (nl + den - 1) / den else nl / den + 1
  let cmax := if I.incl then nh / den else (nh + den - 1) / den - 1
  (cmin, cmax)

/-- Some multiple of `r^j` lies in `I`. -/
def hasMultiple (r : Nat) (I : Interval) (j : Int) : Bool :=
  let c := candidates r I j
  decide (c.1 ≤ c.2)

/-- Shortest decimal for the positive double `m * 2^e`: `(s, j)` with `s * 10^j` rounding to the
double, the digit count of `s` minimal, and among those `s * 10^j` closest to the double (ties:
even `s`), as in ECMA-262 Number::toString note 2 and V8. -/
def shortest (m : Nat) (e : Int) : Nat × Int :=
  let I := interval m e
  let d := log10Estimate m e
  let j := searchMax (hasMultiple 10 I) 8 (d - 20) (d + 3)
  let (cmin, cmax) := candidates 10 I j
  let (nx, dx) := scaled 10 (4 * m) I.eb j
  (max cmin (min (roundHalfEven nx dx) cmax), j)

/-! ## Number::toString -/

/-- Exponent suffix `e+n` / `e-n`. -/
def expSuffix (e : Int) : List UInt16 := 101 :: (if e < 0 then 45 else 43) :: natDigits 10 e.natAbs

/-- Number::toString layout (steps 6–12) for the digits `ds` of `s` (`k = ds.length`) and the
decimal point position `n` (value `s * 10^(n-k)`). -/
def layout (ds : List UInt16) (n : Int) : List UInt16 :=
  let k : Int := ds.length
  if k ≤ n ∧ n ≤ 21 then ds ++ List.replicate (n - k).toNat 48
  else if 0 < n ∧ n ≤ 21 then ds.take n.toNat ++ 46 :: ds.drop n.toNat
  else if -6 < n ∧ n ≤ 0 then 48 :: 46 :: (List.replicate (-n).toNat 48 ++ ds)
  else
    match ds with
    | [] => expSuffix (n - 1)
    | [d] => d :: expSuffix (n - 1)
    | d :: rest => d :: 46 :: (rest ++ expSuffix (n - 1))

/-- Number::toString of the positive double `m * 2^e` through the shortest-digit search. -/
def magGeneral (m : Nat) (e : Int) : List UInt16 :=
  let (s, j) := shortest m e
  let ds := natDigits 10 s
  layout ds (j + ds.length)

/-- Number::toString of the positive double `m * 2^e`. Integers below `2^53` print exactly (their
shortest representation is the integer itself), everything else through `magGeneral`. -/
def magString (m : Nat) (e : Int) : List UInt16 :=
  match intValue? m e with
  | some v => if v < 2 ^ 53 then natDigits 10 v else magGeneral m e
  | none => magGeneral m e

/-- `Number::toString(x)` (radix 10), i.e. `String(x)` and template-literal interpolation. -/
def toJSString : F64 → JSStr
  | .nan => "NaN"
  | .inf neg => if neg then "-Infinity" else "Infinity"
  | .fin x => if x.man = 0 then "0" else ⟨(if x.neg then [45] else []) ++ magString x.man x.exp⟩

/-! ## toFixed, toExponential, toPrecision -/

/-- `m * 2^e ≥ 10^21`. -/
def geE21 (m : Nat) (e : Int) : Bool := pow10Le m e 21

/-- `x.toFixed(f)`; `none` is the RangeError for `f > 100`. Ties round away from zero
(the spec's "larger n"), values with `|x| ≥ 10^21` fall back to `ToString`. -/
def toFixed (x : F64) (f : Nat) : Option JSStr :=
  if 100 < f then none
  else some <| match x with
    | .nan => "NaN"
    | .inf neg => if neg then "-Infinity" else "Infinity"
    | .fin x =>
      let sgn : List UInt16 := if x.neg && x.man != 0 then [45] else []
      if x.man != 0 && geE21 x.man x.exp then ⟨sgn ++ magString x.man x.exp⟩
      else
        let ds := natDigits 10 (scaledRound x.man x.exp f)
        if f = 0 then ⟨sgn ++ ds⟩
        else
          let ds := if ds.length ≤ f then List.replicate (f + 1 - ds.length) 48 ++ ds else ds
          let a := ds.length - f
          ⟨sgn ++ ds.take a ++ 46 :: ds.drop a⟩

/-- Digits of `m * 2^e` (`m > 0`) rounded half up to `p ≥ 1` significant digits: `(n, d)` with
`10^(p-1) ≤ n < 10^p` and value `n * 10^(d-p+1)`. -/
def roundSig (m : Nat) (e : Int) (p : Nat) : Nat × Int :=
  let d := log10Floor m e
  let n := scaledRound m e ((p : Int) - 1 - d)
  if n = 10 ^ p then (10 ^ (p - 1), d + 1) else (n, d)

/-- Mantissa `d` or `d.ddd` of the exponential forms. -/
def pointAfterFirst : List UInt16 → List UInt16
  | [] => []
  | [d] => [d]
  | d :: rest => d :: 46 :: rest

/-- `x.toExponential(f)`; `f = none` is `undefined` (as many digits as necessary, i.e. the
shortest round-trip digits). `none` is the RangeError for `f > 100` (checked after the
non-finite cases, as in the spec). -/
def toExponential (x : F64) (f : Option Nat) : Option JSStr :=
  match x with
  | .nan => some "NaN"
  | .inf neg => some (if neg then "-Infinity" else "Infinity")
  | .fin x =>
    let sgn : List UInt16 := if x.neg && x.man != 0 then [45] else []
    let res (ds : List UInt16) (e : Int) : Option JSStr :=
      some ⟨sgn ++ pointAfterFirst ds ++ expSuffix e⟩
    match f with
    | some f =>
      if 100 < f then none
      else if x.man = 0 then res (List.replicate (f + 1) 48) 0
      else
        let (n, d) := roundSig x.man x.exp (f + 1)
        res (natDigits 10 n) d
    | none =>
      if x.man = 0 then res [48] 0
      else
        let (s, j) := shortest x.man x.exp
        let ds := natDigits 10 s
        res ds (j + ds.length - 1)

/-- `x.toPrecision(p)`; `none` is the RangeError for `p < 1 ∨ p > 100` (checked after the
non-finite cases). `x.toPrecision(undefined)` is `toJSString x`. -/
def toPrecision (x : F64) (p : Nat) : Option JSStr :=
  match x with
  | .nan => some "NaN"
  | .inf neg => some (if neg then "-Infinity" else "Infinity")
  | .fin x =>
    if p < 1 ∨ 100 < p then none
    else
      let sgn : List UInt16 := if x.neg && x.man != 0 then [45] else []
      let (ds, e) : List UInt16 × Int :=
        if x.man = 0 then (List.replicate p 48, 0)
        else let (n, d) := roundSig x.man x.exp p; (natDigits 10 n, d)
      if e < -6 ∨ (p : Int) ≤ e then some ⟨sgn ++ pointAfterFirst ds ++ expSuffix e⟩
      else if e = (p : Int) - 1 then some ⟨sgn ++ ds⟩
      else if 0 ≤ e then some ⟨sgn ++ ds.take (e + 1).toNat ++ 46 :: ds.drop (e + 1).toNat⟩
      else some ⟨sgn ++ 48 :: 46 :: (List.replicate (-(e + 1)).toNat 48 ++ ds)⟩

/-! ## Radix conversion (V8's double arithmetic reproduced exactly) -/

/-- Nearest double to `num / den * 2^e` (round half to even; `den > 0`). -/
def roundRat (neg : Bool) (num den : Nat) (e : Int) : F64 :=
  if num = 0 then F64.zero neg
  else
    let sh : Int := (bitLen den : Int) - bitLen num + 56
    let n' := num * 2 ^ sh.toNat
    let d' := den * 2 ^ (-sh).toNat
    F64.round neg (n' / d') (e - sh) (n' % d' != 0)

/-- Exact value `(m, e)` (`= m * 2^e`, sign dropped) of a finite double; `(0, 0)` otherwise. -/
def dyadic : F64 → Nat × Int
  | .fin x => (x.man, x.exp)
  | _ => (0, 0)

/-- IEEE `a / r` for `a = m * 2^e ≥ 0`. -/
def dyDiv (a : Nat × Int) (r : Nat) : Nat × Int := dyadic (roundRat false a.1 r a.2)

/-- IEEE `a - b` for `a ≥ b ≥ 0`. -/
def dySub (a b : Nat × Int) : Nat × Int :=
  let e := min a.2 b.2
  dyadic (F64.round false (a.1 * 2 ^ (a.2 - e).toNat - b.1 * 2 ^ (b.2 - e).toNat) e)

/-- `fmod(a, r)` (exact). -/
def dyMod (a : Nat × Int) (r : Nat) : Nat × Int :=
  if 0 ≤ a.2 then ((a.1 * 2 ^ a.2.toNat) % r, 0) else (a.1 % (r * 2 ^ (-a.2).toNat), a.2)

/-- `⌊a⌋`. -/
def dyFloor (a : Nat × Int) : Nat :=
  if 0 ≤ a.2 then a.1 * 2 ^ a.2.toNat else a.1 / 2 ^ (-a.2).toNat

/-- `a ≥ 2^53`. -/
def dyGe53 (a : Nat × Int) : Bool := decide (2 ^ 53 * 2 ^ (-a.2).toNat ≤ a.1 * 2 ^ a.2.toNat)

/-- Integer digits printed by V8's `DoubleToRadixCString` for a non-negative integral double
`v = m * 2^e`: while the double quotient `v / r` is at least `2^53`, emit a `0` and divide;
then `digit = fmod(v, r)`, `v = (v - digit) / r` in double arithmetic. Exact for `v < 2^53` and
for power-of-two radices; for other radices larger values print rounded digits (this is what
Node prints; it is not the spec's shortest round-trip representation). -/
def v8RadixInt (r : Nat) (v : Nat × Int) : List UInt16 :=
  let (v', zeros) := fill 1100 v
  digitsLoop 1200 v' [] ++ List.replicate zeros 48
where
  fill : Nat → Nat × Int → (Nat × Int) × Nat
    | 0, v => (v, 0)
    | fuel + 1, v =>
      let q := dyDiv v r
      if dyGe53 q then let (w, z) := fill fuel q; (w, z + 1) else (v, 0)
  digitsLoop : Nat → Nat × Int → List UInt16 → List UInt16
    | 0, _, acc => acc
    | fuel + 1, v, acc =>
      let rem := dyMod v r
      let acc := digitUnit (dyFloor rem) :: acc
      let v' := dyDiv (dySub v rem) r
      if v'.1 = 0 then acc else digitsLoop fuel v' acc

/-- `x.toString(r)`: `none` is the RangeError for `r ∉ [2, 36]` and, for `r ≠ 10`, the
non-integral finite values (implementation-approximated, not modelled). Integral values print
as Node prints them (`v8RadixInt`). -/
def toStringRadix (x : F64) (r : Nat) : Option JSStr :=
  if r < 2 ∨ 36 < r then none
  else if r = 10 then some (toJSString x)
  else match x with
    | .nan => some "NaN"
    | .inf neg => some (if neg then "-Infinity" else "Infinity")
    | .fin x =>
      if x.man = 0 then some "0"
      else match intValue? x.man x.exp with
        | none => none
        | some v =>
          some ⟨(if x.neg then [45] else []) ++
            (if v < 2 ^ 53 then natDigits r v else v8RadixInt r (x.man, x.exp))⟩

/-! ## BigInt and Boolean -/

/-- `x.toString()` for a BigInt. -/
def bigintToJSString (x : Int) : JSStr := ⟨(if x < 0 then [45] else []) ++ natDigits 10 x.natAbs⟩

/-- `x.toString(r)` for a BigInt; `none` is the RangeError for `r ∉ [2, 36]`. -/
def bigintToStringRadix (x : Int) (r : Nat) : Option JSStr :=
  if r < 2 ∨ 36 < r then none else some ⟨(if x < 0 then [45] else []) ++ natDigits r x.natAbs⟩

/-- `String(b)`. -/
def boolToJSString (b : Bool) : JSStr := if b then "true" else "false"

end NumFormat
end StrictTS
