/-!
  Exact IEEE 754 binary64 operations on the bits of a `Float`, for the
  semantics and the C library models.

  Lean's `Float` has a logical model (its bit pattern, `Float.toBits`), so the
  definitions here reduce in the kernel, unlike `Float.floor`,
  `Float.toFloat32`, ... (calls into the C library, opaque to the kernel). A
  finite double is `(-1)^neg · m · 2^e` (`decodeF`). Comparisons, truncation
  and rounding to integers, rounding to `float`, `fmod` and decimal output
  (`printf`'s `%e %f %g`) are computed exactly from it; decimal and
  hexadecimal input (`strtod`, `scanf`) is rounded correctly (to nearest,
  ties to even).
-/

namespace CIR.Std

/-- A floating-point value: `finite neg m e` is `(-1)^neg · m · 2^e`. -/
inductive FVal where
  | finite (neg : Bool) (m : Nat) (e : Int)
  | inf (neg : Bool)
  | nan
  deriving Repr, DecidableEq, Inhabited

/-- The value of binary64 bits. -/
def decodeBits (b : Nat) : FVal :=
  let neg := decide (2 ^ 63 ≤ b)
  let be : Nat := b / 2 ^ 52 % 2048
  let fr : Nat := b % 2 ^ 52
  if be = 2047 then (if fr = 0 then .inf neg else .nan)
  else if be = 0 then .finite neg fr (-1074)
  else .finite neg (fr + 2 ^ 52) ((be : Int) - 1075)

/-- The value of a double. -/
def decodeF (x : Float) : FVal := decodeBits x.toBits.toNat

/-- A value as an integer multiple of `2^-1074` (exact for doubles), the
infinities beyond every finite double; `none` for NaN. IEEE comparisons are
comparisons of keys (`-0 = +0`, NaN unordered). -/
def fkey : FVal → Option Int
  | .finite neg m e =>
    let k : Int := m * 2 ^ (e + 1074).toNat
    some (if neg then -k else k)
  | .inf neg => some (if neg then -2 ^ 2100 else 2 ^ 2100)
  | .nan => none

/-! ### Rounding a rational to a binary format -/

/-- `⌊log₂ (num / den)⌋` for positive `num`, `den`. -/
def log2Q (num den : Nat) : Int :=
  let l : Int := (Nat.log2 num : Int) - Nat.log2 den
  let ok := if 0 ≤ l then decide (den * 2 ^ l.toNat ≤ num) else decide (den ≤ num * 2 ^ (-l).toNat)
  if ok then l else l - 1

/-- `num / den` rounded to an integer, ties to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r < den then q else if den < 2 * r then q + 1 else q + q % 2

/-- `num / den / 2^e` rounded to an integer, ties to even. -/
def roundScaled (num den : Nat) (e : Int) : Nat :=
  if 0 ≤ e then roundHalfEven num (den * 2 ^ e.toNat) else roundHalfEven (num * 2 ^ (-e).toNat) den

/-- The rational `num / den` rounded to `p` significant bits with exponents
at least `emin` (the quantum of the subnormals), to nearest, ties to even:
`some (m, e)` with `m < 2^p`, value `m · 2^e`, or `none` when the exponent
exceeds `emax` (overflow: infinity). -/
def roundBin (p : Nat) (emin emax : Int) (num den : Nat) : Option (Nat × Int) :=
  if num = 0 then some (0, emin) else
  let e := max (log2Q num den - (p - 1 : Nat)) emin
  let m := roundScaled num den e
  let (m, e) := if m = 2 ^ p then (2 ^ (p - 1), e + 1) else (m, e)
  if emax < e then none else some (m, e)

/-- binary64 bits of a sign and a result of `roundBin 53 (-1074) 971`
(`none`: infinity). -/
def bitsOf (neg : Bool) : Option (Nat × Int) → Nat
  | none => (if neg then 2 ^ 63 else 0) + 2047 * 2 ^ 52
  | some (m, e) =>
    let s := if neg then 2 ^ 63 else 0
    -- below 2^52 only for subnormals and zero (exponent `-1074`, biased 0)
    if m < 2 ^ 52 then s + m else s + (e + 1075).toNat * 2 ^ 52 + (m - 2 ^ 52)

/-- The double nearest to `(-1)^neg · num / den` (ties to even; infinity
beyond the largest double). -/
def ratToFloat (neg : Bool) (num den : Nat) : Float :=
  Float.ofBits (bitsOf neg (roundBin 53 (-1074) 971 num den)).toUInt64

/-- The double nearest to `(-1)^neg · m · 2^e` (the value itself when it is
representable). -/
def valToFloat (neg : Bool) (m : Nat) (e : Int) : Float :=
  ratToFloat neg (m * 2 ^ e.toNat) (2 ^ (-e).toNat)

def nanF : Float := Float.ofBits 0x7FF8000000000000

def infF (neg : Bool) : Float := Float.ofBits (bitsOf neg none).toUInt64

/-- The `float` (binary32) nearest to `(-1)^neg · num / den`, as a double. -/
def ratToSingle (neg : Bool) (num den : Nat) : Float :=
  match roundBin 24 (-149) 104 num den with
  | some (m, e) => valToFloat neg m e
  | none => infF neg

/-- A double rounded to `float` (binary32), as a double. -/
def roundSingle (x : Float) : Float :=
  match decodeF x with
  | .finite neg m e => ratToSingle neg (m * 2 ^ e.toNat) (2 ^ (-e).toNat)
  | _ => x

/-- An integer converted to `float`: rounded once, to binary32. -/
def intToSingle (v : Int) : Float := ratToSingle (decide (v < 0)) v.natAbs 1

/-! ### binary32 bit patterns -/

/-- binary32 bits of a sign and a result of `roundBin 24 (-149) 104`
(`none`: infinity). -/
def bitsOf32 (neg : Bool) : Option (Nat × Int) → Nat
  | none => (if neg then 2 ^ 31 else 0) + 255 * 2 ^ 23
  | some (m, e) =>
    let s := if neg then 2 ^ 31 else 0
    -- below 2^23 only for subnormals and zero (exponent `-149`, biased 0)
    if m < 2 ^ 23 then s + m else s + (e + 150).toNat * 2 ^ 23 + (m - 2 ^ 23)

/-- The binary32 bit pattern of a `float` (kept as a double, `roundSingle`d).
`Float` has a single NaN (no sign, no payload): it gives the quiet NaN
`0x7FC00000`. -/
def singleToBits (x : Float) : Nat :=
  match decodeF x with
  | .finite neg m e => bitsOf32 neg (roundBin 24 (-149) 104 (m * 2 ^ e.toNat) (2 ^ (-e).toNat))
  | .inf neg => bitsOf32 neg none
  | .nan => 255 * 2 ^ 23 + 2 ^ 22

/-- The `float` (as a double) with binary32 bit pattern `b < 2^32`: every NaN
pattern gives the NaN, the others their exact value. -/
def singleOfBits (b : Nat) : Float :=
  let neg := decide (2 ^ 31 ≤ b)
  let be : Nat := b / 2 ^ 23 % 256
  let fr : Nat := b % 2 ^ 23
  if be = 255 then (if fr = 0 then infF neg else nanF)
  else if be = 0 then valToFloat neg fr (-149)
  else valToFloat neg (fr + 2 ^ 23) ((be : Int) - 150)

/-! ### Integers -/

/-- The integer part (toward zero) of a finite value. -/
def truncVal (neg : Bool) (m : Nat) (e : Int) : Int :=
  let a : Nat := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
  if neg then -(a : Int) else a

/-- `floor` (`mode` 0), `ceil` (1), `trunc` (2), `round` (3: half away
from zero) and `rint` / `nearbyint` in the default rounding mode (4: to
nearest, half to even) of a double, exactly; the sign of a zero result is the
argument's. -/
def roundIntF (mode : Nat) (x : Float) : Float :=
  match decodeF x with
  | .finite neg m e =>
    if 0 ≤ e then x else
    let k := (-e).toNat
    let q := m / 2 ^ k
    let r := m % 2 ^ k
    let up : Bool := match mode with
      | 0 => neg && r != 0
      | 1 => !neg && r != 0
      | 2 => false
      | 3 => decide (2 ^ k ≤ 2 * r)
      | _ => decide (2 ^ k < 2 * r) || (2 * r == 2 ^ k && q % 2 == 1)
    valToFloat neg (if up then q + 1 else q) 0
  | _ => x

/-- `fmod(x, y)`: `x - n·y` for the integer part `n` of `x / y`, exactly
(C11 7.12.10.1); NaN for `y = 0` or infinite `x`. -/
def fmodF (x y : Float) : Float :=
  match decodeF x, decodeF y with
  | .finite nx mx ex, .finite _ my ey =>
    if my = 0 then nanF else
    let e := min ex ey
    valToFloat nx (mx * 2 ^ (ex - e).toNat % (my * 2 ^ (ey - e).toNat)) e
  | .finite .., .inf _ => x
  | _, _ => nanF

/-! ### Decimal output (`printf`) -/

/-- `num / den / 10^k` rounded to an integer, ties to even. -/
def roundDec (num den : Nat) (k : Int) : Nat :=
  if 0 ≤ k then roundHalfEven num (den * 10 ^ k.toNat) else roundHalfEven (num * 10 ^ (-k).toNat) den

/-- Number of decimal digits of `n` (1 for 0). -/
def decLen (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- `⌊log₁₀ (num / den)⌋` for positive `num`, `den`. -/
def log10Q (num den : Nat) : Int :=
  let ln := decLen num
  let ld := decLen den
  if den * 10 ^ ln ≤ num * 10 ^ ld then (ln : Int) - ld else (ln : Int) - ld - 1

/-- `m · 2^e` to `P` significant decimal digits (`P ≥ 1`): the digits and the
exponent `X` of `d₀.d₁…d_{P-1} · 10^X`, rounded to nearest, ties to even
(glibc rounds the exact binary value in the current rounding mode). `X` is
kept within `[-999, 999]`: a double's is within `[-324, 308]`, and the bound
makes the printed exponent at most three digits by construction. -/
def sciDigits (P : Nat) (m : Nat) (e : Int) : List Nat × Int :=
  let num := m * 2 ^ e.toNat
  let den := 2 ^ (-e).toNat
  if num = 0 then (List.replicate P 0, 0) else
  let X := log10Q num den
  let N := roundDec num den (X + 1 - P)
  let (N, X) := if N = 10 ^ P then (10 ^ (P - 1), X + 1) else (N, X)
  ((List.range P).map (fun i => N / 10 ^ (P - 1 - i) % 10), max (-999) (min 999 X))

def digitChars (ds : List Nat) : List Int := ds.map fun d => Int.ofNat d + 48

/-- Decimal digits of `n`, as characters. -/
def natChars (n : Nat) : List Int := (Nat.toDigits 10 n).map fun c => (c.toNat : Int)

/-- The exponent of `%e`: `e`, its sign and at least two digits. -/
def expChars (upper : Bool) (X : Int) : List Int :=
  let a := X.natAbs
  (if upper then 69 else 101) :: (if X < 0 then 45 else 43) ::
    (if a < 10 then [48, (a : Int) + 48]
     else if a < 100 then [(a / 10 : Nat) + 48, (a % 10 : Nat) + 48]
     else if a < 1000 then [(a / 100 : Nat) + 48, (a / 10 % 10 : Nat) + 48, (a % 10 : Nat) + 48]
     else natChars a)

/-- Digits without their trailing zeros. -/
def stripZeros (ds : List Nat) : List Nat := (ds.reverse.dropWhile (· == 0)).reverse

/-- `%e` (`%E`) of `m · 2^e` with precision `prec`; `alt`: the `#` flag. -/
def fmtE (alt upper : Bool) (prec : Nat) (m : Nat) (e : Int) : List Int :=
  let (ds, X) := sciDigits (prec + 1) m e
  digitChars (ds.take 1) ++ (if prec = 0 && !alt then [] else 46 :: digitChars (ds.drop 1)) ++
    expChars upper X

/-- `%f` of `m · 2^e` with precision `prec`. -/
def fmtF (alt : Bool) (prec : Nat) (m : Nat) (e : Int) : List Int :=
  let N := roundDec (m * 2 ^ e.toNat) (2 ^ (-e).toNat) (-(prec : Int))
  let fp := N % 10 ^ prec
  natChars (N / 10 ^ prec) ++
    (if prec = 0 && !alt then []
     else 46 :: digitChars ((List.range prec).map fun i => fp / 10 ^ (prec - 1 - i) % 10))

/-- `%g` (`%G`) of `m · 2^e` with precision `prec` (C11 7.21.6.1p8): style
`f` if the exponent `X` of style `e` satisfies `-4 ≤ X < P`, else style `e`,
with `P` significant digits; trailing zeros removed unless `#`. As glibc,
with `#`, a value whose rounding carries from `X = P - 1` to `X = P` is
printed with no fraction digits (`%#g` of 999999.9999 is `1.e+06`). -/
def fmtG (alt upper : Bool) (prec : Nat) (m : Nat) (e : Int) : List Int :=
  let P := if prec = 0 then 1 else prec
  let (ds, X) := sciDigits P m e
  let num := m * 2 ^ e.toNat
  if alt && num != 0 && X == (P : Int) && log10Q num (2 ^ (-e).toNat) + 1 == X then
    digitChars (ds.take 1) ++ 46 :: expChars upper X
  else if -4 ≤ X ∧ X < P then
    let (ip, fp) := if 0 ≤ X then (ds.take (X.toNat + 1), ds.drop (X.toNat + 1))
      else ([0], List.replicate ((-X).toNat - 1) 0 ++ ds)
    let fp := if alt then fp else stripZeros fp
    digitChars ip ++ (if fp.isEmpty && !alt then [] else 46 :: digitChars fp)
  else
    let fp := if alt then ds.drop 1 else stripZeros (ds.drop 1)
    digitChars (ds.take 1) ++ (if fp.isEmpty && !alt then [] else 46 :: digitChars fp) ++
      expChars upper X

/-- The sign and the body of a floating-point conversion (`c` one of
`f F e E g G`) of `x`: `none` for NaN (glibc prints its sign bit, which the
logical model of `Float` does not keep). `plus`/`space`: the `+` and ` `
flags; `prec`: the precision (default 6). -/
def fmtFloat (c : Int) (alt plus space : Bool) (prec : Option Nat) (x : Float) :
    Option (List Int × List Int) :=
  let upper := c == 70 || c == 69 || c == 71
  let sign (neg : Bool) : List Int := if neg then [45] else if plus then [43] else if space then [32] else []
  match decodeF x with
  | .nan => none
  | .inf neg => some (sign neg, if upper then [73, 78, 70] else [105, 110, 102])
  | .finite neg m e =>
    let p := prec.getD 6
    let body := if c == 102 || c == 70 then fmtF alt p m e
      else if c == 101 || c == 69 then fmtE alt upper p m e
      else fmtG alt upper p m e
    some (sign neg, body)

/-! ### Decimal and hexadecimal input (`strtod`, `scanf`) -/

def isDigitC (c : Int) : Bool := 48 ≤ c && c ≤ 57

def isHexC (c : Int) : Bool := isDigitC c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)

def hexVal (c : Int) : Nat :=
  if isDigitC c then (c - 48).toNat else if c ≤ 70 then (c - 55).toNat else (c - 87).toNat

def lowerC (c : Int) : Int := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- Length of the longest prefix of `cs` that equals a prefix of `w`
(lowercase letters), ignoring case. -/
def matchWord : List Int → List Int → Nat
  | c :: cs, w :: ws => if lowerC c == w then matchWord cs ws + 1 else 0
  | _, _ => 0

/-- `cs` starts with `0x` or `0X`. -/
def hexPrefix : List Int → Bool
  | 48 :: x :: _ => x == 120 || x == 88
  | _ => false

/-- A floating-point subject sequence (after any sign), C11 7.22.1.3p3:
`(valid, longest)`: the length of the longest prefix that is a complete
subject sequence (what `strtod` converts), and of the longest prefix that is
a prefix of one (what `scanf` reads before it decides). -/
def fpSubject (cs : List Int) : Nat × Nat :=
  let inf := matchWord cs [105, 110, 102, 105, 110, 105, 116, 121]
  let nan := matchWord cs [110, 97, 110]
  if inf > 0 then (if inf = 8 then (8, 8) else if inf ≥ 3 then (3, inf) else (0, inf))
  else if nan > 0 then
    if nan < 3 then (0, nan) else
      match cs.drop 3 with
      | 40 :: rest =>
        let k := (rest.takeWhile fun c => isDigitC c || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95).length
        if (rest.drop k).head? == some 41 then (k + 5, k + 5) else (3, k + 4)
      | _ => (3, 3)
  else
    let hex := hexPrefix cs
    let dig := if hex then isHexC else isDigitC
    let rest := if hex then cs.drop 2 else cs
    let ki := (rest.takeWhile dig).length
    let (kf, dot) : Nat × Nat := match rest.drop ki with
      | 46 :: r => ((r.takeWhile dig).length, 1)
      | _ => (0, 0)
    let pre := (if hex then 2 else 0) + ki + dot + kf
    if ki + kf = 0 then
      -- no digits: the subject of `0x` is `0`; `scanf` has read the `0x` and a `.`
      if hex then (1, 2 + dot) else (0, dot)
    else
      let expC : Int := if hex then 112 else 101
      match cs.drop pre with
      | c :: r =>
        if lowerC c == expC then
          let s := match r with
            | 43 :: _ | 45 :: _ => 1
            | _ => 0
          let kd := ((r.drop s).takeWhile isDigitC).length
          if kd = 0 then (pre, pre + 1 + s) else (pre + 1 + s + kd, pre + 1 + s + kd)
        else (pre, pre)
      | [] => (pre, pre)

/-- Value of the decimal digits `ds` (characters). -/
def decDigitsVal (ds : List Int) : Nat := ds.foldl (fun acc c => acc * 10 + (c - 48).toNat) 0

/-- Value of the hexadecimal digits `ds` (characters). -/
def hexDigitsVal (ds : List Int) : Nat := ds.foldl (fun acc c => acc * 16 + hexVal c) 0

/-- Exponent part `e±ddd` / `p±ddd` (the characters after the marker). -/
def expVal (cs : List Int) : Int :=
  match cs with
  | 45 :: ds => -(decDigitsVal (ds.takeWhile isDigitC) : Int)
  | 43 :: ds => decDigitsVal (ds.takeWhile isDigitC)
  | ds => decDigitsVal (ds.takeWhile isDigitC)

/-- The rational `mant · base^x` (`base` 10 or 2) rounded with `round`
(`roundBin` for a format), with the exponent bounded first so that huge
exponents do not compute huge powers: beyond them the value overflows or
rounds to zero in every format. -/
def scaleRound (round : Nat → Nat → Float) (neg : Bool) (mant : Nat) (base : Nat) (x : Int) :
    Float :=
  if mant = 0 then valToFloat neg 0 0
  else if 5000 < x then infF neg
  else if x < -(5000 + 4 * (Nat.log2 mant + 1) : Int) then valToFloat neg 0 0
  else if 0 ≤ x then round (mant * base ^ x.toNat) 1 else round mant (base ^ (-x).toNat)

/-- Value of a complete subject sequence `cs` (after the sign), rounded with
`round`; `neg` the sign. -/
def subjectValue (round : Bool → Nat → Nat → Float) (neg : Bool) (cs : List Int) : Float :=
  match cs with
  | c :: _ =>
    if lowerC c == 105 then infF neg
    else if lowerC c == 110 then nanF
    else
      let hex := hexPrefix cs
      let dig := if hex then isHexC else isDigitC
      let rest := if hex then cs.drop 2 else cs
      let ip := rest.takeWhile dig
      let (fp, after) : List Int × List Int := match rest.drop ip.length with
        | 46 :: r => (r.takeWhile dig, r.drop (r.takeWhile dig).length)
        | r => ([], r)
      if hex then
        if ip.isEmpty && fp.isEmpty then valToFloat neg 0 0 else
        let x : Int := match after with
          | p :: r => if lowerC p == 112 then expVal r else 0
          | [] => 0
        scaleRound (round neg) neg (hexDigitsVal (ip ++ fp)) 2 (x - 4 * fp.length)
      else
        let x : Int := match after with
          | p :: r => if lowerC p == 101 then expVal r else 0
          | [] => 0
        scaleRound (round neg) neg (decDigitsVal (ip ++ fp)) 10 (x - fp.length)
  | [] => valToFloat neg 0 0

/-- `strtod` on `cs` (C11 7.22.1.3): the value (rounded with `round`: to
double or to float) and the number of characters consumed (0 when there is
no subject sequence). -/
def strtodWith (round : Bool → Nat → Nat → Float) (cs : List Int) : Float × Nat :=
  let ws := (cs.takeWhile fun c => c == 32 || (9 ≤ c && c ≤ 13)).length
  let cs1 := cs.drop ws
  let (neg, sgn) : Bool × Nat := match cs1 with
    | 45 :: _ => (true, 1)
    | 43 :: _ => (false, 1)
    | _ => (false, 0)
  let cs2 := cs1.drop sgn
  let (valid, _) := fpSubject cs2
  if valid = 0 then (valToFloat false 0 0, 0)
  else (subjectValue round neg (cs2.take valid), ws + sgn + valid)

end CIR.Std
