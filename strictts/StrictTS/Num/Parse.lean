/-
StrictTS: String to Number / BigInt conversions (ECMA-262 §7.1.4.1.1 StringToNumber,
§19.2.4 parseFloat, §19.2.5 parseInt, §7.1.14 StringToBigInt).

Decimal strings are rounded correctly (round half to even on the exact value), as V8 does;
the spec's optional 20-significant-digit truncation is not used.
-/
import StrictTS.Num.F64
import StrictTS.Str.JSStr
import StrictTS.Num.Format

namespace StrictTS
namespace NumParse

open F64 (bitLen)
open NumFormat (roundRat)

/-- Nearest double to `digits * 10^exp10` (round half to even); an exact zero has the sign `neg`.
Overflow gives `±Infinity`, underflow `±0`. -/
def roundDecimal (neg : Bool) (digits : Nat) (exp10 : Int) : F64 :=
  if digits = 0 then F64.zero neg
  else
    let b : Int := bitLen digits
    if 0 ≤ exp10 then
      -- value ≥ 2^(b-1) * 8^exp10
      if 1025 ≤ b - 1 + 3 * exp10 then .inf neg
      else F64.round neg (digits * 10 ^ exp10.toNat) 0
    else
      -- value < 2^b * 8^exp10
      if b + 3 * exp10 ≤ -1076 then F64.zero neg
      else roundRat neg digits (10 ^ (-exp10).toNat) 0

/-- Value of a digit (`0-9`, `a-z`, `A-Z` ↦ 0–35). -/
def digitVal? (u : UInt16) : Option Nat :=
  let n := u.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 87)
  else if 65 ≤ n ∧ n ≤ 90 then some (n - 55)
  else none

/-- `u` is a digit of radix `r`. -/
def isRadixDigit (r : Nat) (u : UInt16) : Bool := (digitVal? u).any (· < r)

/-- Value of a list of radix-`r` digits. -/
def digitsValue (r : Nat) (ds : List UInt16) : Nat :=
  ds.foldl (fun acc u => acc * r + (digitVal? u).getD 0) 0

/-- `Infinity`. -/
def infinityUnits : List UInt16 := [73, 110, 102, 105, 110, 105, 116, 121]

/-- Longest prefix of `l` that is a StrUnsignedDecimalLiteral other than `Infinity`:
`(significand, exp10, rest)` with value `significand * 10^exp10`. -/
def unsignedDecimalPrefix (l : List UInt16) : Option (Nat × Int × List UInt16) :=
  let intDs := l.takeWhile (isRadixDigit 10)
  let r1 := l.drop intDs.length
  let (fracDs, r2) : List UInt16 × List UInt16 :=
    match r1 with
    | 46 :: t => let fd := t.takeWhile (isRadixDigit 10); (fd, t.drop fd.length)
    | _ => ([], r1)
  if intDs.isEmpty && fracDs.isEmpty then none
  else
    let mant := digitsValue 10 (intDs ++ fracDs)
    let e0 : Int := -(fracDs.length : Int)
    match r2 with
    | c :: t =>
      if c == 101 || c == 69 then
        let (eneg, t') : Bool × List UInt16 :=
          match t with
          | 43 :: t' => (false, t')
          | 45 :: t' => (true, t')
          | _ => (false, t)
        let eds := t'.takeWhile (isRadixDigit 10)
        if eds.isEmpty then some (mant, e0, r2)
        else
          let ev : Int := digitsValue 10 eds
          some (mant, e0 + (if eneg then -ev else ev), t'.drop eds.length)
      else some (mant, e0, r2)
    | [] => some (mant, e0, [])

/-- Radix of a `0x`/`0o`/`0b` prefix letter (either case). -/
def prefixRadix? (u : UInt16) : Option Nat :=
  if u == 120 || u == 88 then some 16
  else if u == 111 || u == 79 then some 8
  else if u == 98 || u == 66 then some 2
  else none

/-- NonDecimalIntegerLiteral (whole string, no sign, no separators): its exact value. -/
def nonDecimalValue? (l : List UInt16) : Option Nat :=
  match l with
  | 48 :: p :: ds =>
    match prefixRadix? p with
    | some r => if !ds.isEmpty && ds.all (isRadixDigit r) then some (digitsValue r ds) else none
    | none => none
  | _ => none

/-- Optional leading sign. -/
def splitSign (l : List UInt16) : Bool × List UInt16 :=
  match l with
  | 43 :: t => (false, t)
  | 45 :: t => (true, t)
  | _ => (false, l)

/-- `Number(s)` (StringToNumber): StrWhiteSpace trimmed, `""` ↦ `+0`, `±Infinity`, decimal
literals with optional exponent, `0x`/`0o`/`0b` integers without sign, anything else `NaN`. -/
def stringToNumber (s : JSStr) : F64 :=
  let t := s.trim.units
  if t.isEmpty then F64.zero false
  else match nonDecimalValue? t with
    | some v => F64.round false v 0
    | none =>
      let (neg, body) := splitSign t
      if body == infinityUnits then .inf neg
      else match unsignedDecimalPrefix body with
        | some (mant, e10, []) => roundDecimal neg mant e10
        | _ => .nan

/-- `parseFloat(s)`: the longest StrDecimalLiteral prefix after leading white space. -/
def parseFloat (s : JSStr) : F64 :=
  let (neg, body) := splitSign s.trimStart.units
  if infinityUnits.isPrefixOf body then .inf neg
  else match unsignedDecimalPrefix body with
    | some (mant, e10, _) => roundDecimal neg mant e10
    | none => .nan

/-- Exact IEEE `a * M` for a non-negative double `a` and a natural number `M`. -/
def mulNat (a : F64) (M : Nat) : F64 :=
  match a with
  | .fin x => F64.round false (x.man * M) x.exp
  | a => a

/-- Exact IEEE `a + p` for a non-negative double `a` and a natural number `p`. -/
def addNat (a : F64) (p : Nat) : F64 :=
  match a with
  | .fin x =>
    let e := min x.exp 0
    F64.round false (x.man * 2 ^ (x.exp - e).toNat + p * 2 ^ (-e).toNat) e
  | a => a

/-- Fused `a * M + p` (one rounding) for a non-negative double `a` and natural numbers `M`, `p`. -/
def fmaNat (a : F64) (M p : Nat) : F64 :=
  match a with
  | .fin x =>
    let e := min x.exp 0
    F64.round false (x.man * M * 2 ^ (x.exp - e).toNat + p * 2 ^ (-e).toNat) e
  | a => a

/-- Digits per chunk in V8's generic-radix `parseInt`: the largest `k` with
`r^k ≤ 0xFFFFFFFF / 36`. -/
def chunkLen (r : Nat) : Nat := go 0 1 32
where
  go (k mult : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if mult * r ≤ 119304647 then go (k + 1) (mult * r) fuel else k

/-- V8's `parseInt` accumulation for radices other than 2, 4, 8, 10, 16, 32 (allowed by the spec
to be implementation-approximated): chunks of `chunkLen r` digits are read exactly and folded in
with `result = result * r^len + part` in double arithmetic. V8's source writes a plain multiply
and add; the Node 22 x64 build used for testing evaluates it fused (one rounding, `fused = true`),
a build without floating-point contraction rounds twice (`fused = false`). -/
def v8GenericRadix (r : Nat) (ds : List UInt16) (fused : Bool := true) : F64 :=
  go (ds.length + 1) ds (F64.zero false)
where
  go : Nat → List UInt16 → F64 → F64
    | 0, _, acc => acc
    | fuel + 1, ds, acc =>
      if ds.isEmpty then acc
      else
        let k := chunkLen r
        let part := ds.take k
        let mult := r ^ part.length
        let p := digitsValue r part
        go fuel (ds.drop k) (if fused then fmaNat acc mult p else addNat (mulNat acc mult) p)

/-- Negation (`-x`). -/
def neg : F64 → F64
  | .nan => .nan
  | .inf b => .inf (!b)
  | .fin x => F64.mkFin (!x.neg) x.man x.exp

/-- `parseInt(s, radix)`, `radix` being `ToInt32(radix)` (`undefined` ↦ `0`). Radix 10 and the
power-of-two radices round correctly; other radices reproduce V8's double accumulation. -/
def parseInt (s : JSStr) (radix : Int) : F64 :=
  let (sgn, S) := splitSign s.trimStart.units
  if radix ≠ 0 ∧ (radix < 2 ∨ 36 < radix) then .nan
  else
    let R : Nat := if radix = 0 then 10 else radix.toNat
    let (R, S) : Nat × List UInt16 :=
      if radix = 0 ∨ radix = 16 then
        match S with
        | 48 :: x :: t => if x == 120 || x == 88 then (16, t) else (R, S)
        | _ => (R, S)
      else (R, S)
    let Z := S.takeWhile (isRadixDigit R)
    if Z.isEmpty then .nan
    else if R = 10 ∨ R = 2 ∨ R = 4 ∨ R = 8 ∨ R = 16 ∨ R = 32 then
      F64.round sgn (digitsValue R Z) 0
    else
      -- V8 skips leading zeros before chunking
      let v := v8GenericRadix R (Z.dropWhile (· == 48))
      if sgn then neg v else v

/-- `BigInt(s)` (StringToBigInt); `none` is the SyntaxError. White space is trimmed, `""` ↦ `0`,
decimal digits may carry a sign, `0x`/`0o`/`0b` literals may not. -/
def stringToBigInt (s : JSStr) : Option Int :=
  let t := s.trim.units
  if t.isEmpty then some 0
  else match nonDecimalValue? t with
    | some v => some v
    | none =>
      let (neg, body) := splitSign t
      if !body.isEmpty && body.all (isRadixDigit 10) then
        let v : Int := digitsValue 10 body
        some (if neg then -v else v)
      else none

end NumParse
end StrictTS
