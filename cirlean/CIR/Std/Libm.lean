import CIR.Std.Complex

/-!
  Functions of the C math library that Lean's `Float` has no operation for, computed as glibc
  2.43 computes them on the reference machine, bit for bit. There glibc's libm is built for
  x86-64-v3: `__FP_FAST_FMA` is defined, so the code takes its fused multiply-add paths, and GCC
  fuses a product into an adjacent sum wherever it can. Each step is an IEEE binary64 operation in
  the order of the compiled code: `Float`'s `+ - * /` and `sqrt` are correctly rounded, a fused
  multiply-add is `fmaF` (rounded once), comparisons are exact (`ltF`, `leF`). A NaN is the single
  NaN of `Float`: glibc's distinction of signaling NaNs is not modelled.
-/

namespace CIR.Std

/-- `0x1p-600`, `0x1p+511`, `0x1p-459`, `0x1p-54`: the scale, the limits and the ratio of
glibc's `hypot`. -/
def hypotScale : Float := Float.ofBits 0x1A70000000000000
def hypotLarge : Float := Float.ofBits 0x5FE0000000000000
def hypotTiny : Float := Float.ofBits 0x2340000000000000
def hypotEps : Float := Float.ofBits 0x3C90000000000000

/-- glibc 2.43's `hypot` kernel (`sysdeps/ieee754/dbl-64/e_hypot.c`), its `__FP_FAST_FMA` version:
`sqrt (ax² + ay²)` with the sum fused, as `2·ay·ax + (ax - ay)²` when `2·ay ≥ ax` (then
`ax - ay` is exact), for `ax ≥ ay ≥ 0` scaled so that the squares neither overflow nor
underflow. -/
def hypotKernel (ax ay : Float) : Float :=
  let t1 := ay + ay
  let t2 := ax - ay
  if leF ax t1 then (fmaF false t1 ax (t2 * t2)).sqrt
  else (fmaF false ax ax (ay * ay)).sqrt

/-- glibc 2.43's `hypot(x, y)`: `+∞` if either is infinite (a NaN's quietness aside), a NaN if
either is a NaN; else the kernel on `|x|`, `|y|` ordered, scaled by `2^-600` above `2^511` and
by `2^600` below `2^-459`, or the sum when the smaller is below `2^-54` times the larger. -/
def hypotF (x y : Float) : Float :=
  if !isFiniteF x || !isFiniteF y then
    if isInfF x || isInfF y then infF false else x + y
  else
    let x := fabsF x
    let y := fabsF y
    let ax := if ltF x y then y else x
    let ay := if ltF x y then x else y
    if ltF hypotLarge ax then
      if leF ay (ax * hypotEps) then ax + ay
      else hypotKernel (ax * hypotScale) (ay * hypotScale) / hypotScale
    else if ltF ay hypotTiny then
      if leF (ay / hypotEps) ax then ax + ay
      else hypotKernel (ax / hypotScale) (ay / hypotScale) * hypotScale
    else if leF ay (ax * hypotEps) then ax + ay
    else hypotKernel ax ay

/-- glibc 2.43's `hypotf(x, y)` (`sysdeps/ieee754/flt-32/e_hypotf.c`): `(float) sqrt ((double) x *
x + (double) y * y)`, the squares exact in `double` (so fusing one into the sum changes nothing),
then rounded to `float`; `+∞` and NaN as `hypot`. The operands are `float`s, kept as `Float`s
rounded to binary32. -/
def hypotfF (x y : Float) : Float :=
  if !isFiniteF x || !isFiniteF y then
    if isInfF x || isInfF y then infF false else roundSingle (x + y)
  else roundSingle (x * x + y * y).sqrt

/-! ### Words of a double -/

/-- The high 32 bits of a double. -/
def hiWord (x : Float) : Nat := (x.toBits >>> 32).toNat

/-- The high word as a signed 32-bit integer (`GET_HIGH_WORD` into an `int32_t`). -/
def hiWordInt (x : Float) : Int :=
  let h := hiWord x
  if 2 ^ 31 ≤ h then (h : Int) - 2 ^ 32 else h

/-- `x` with its high word replaced by `h` modulo `2^32`, its low word kept (`SET_HIGH_WORD`). -/
def withHiWord (x : Float) (h : Int) : Float :=
  let w : Nat := (h % 2 ^ 32).toNat
  Float.ofBits (UInt64.ofNat (w * 2 ^ 32 + x.toBits.toNat % 2 ^ 32))

/-- An integer converted to `double` (exact for the small integers used here). -/
def intToF (k : Int) : Float := valToFloat (decide (k < 0)) k.natAbs 0

/-! ### `expm1` -/

/-- `ln 2` split as `ln2Hi + ln2Lo` (`ln2Hi` with 32 significant bits), `1 / ln 2`, and the
largest argument of `expm1` (and `exp`) whose result is finite, as in fdlibm. -/
def ln2Hi : Float := Float.ofBits 0x3FE62E42FEE00000
def ln2Lo : Float := Float.ofBits 0x3DEA39EF35793C76
def invLn2 : Float := Float.ofBits 0x3FF71547652B82FE
def expm1Over : Float := Float.ofBits 0x40862E42FEFA39EF

/-- fdlibm's `1e-300`, which `expm1` subtracts 1 from for a large negative argument. -/
def expm1Tiny : Float := Float.ofBits 0x01A56E1FC2F8F359

/-- The scaled coefficients `Q1` to `Q5` of fdlibm's `expm1`. -/
def expm1Q1 : Float := Float.ofBits 0xBFA11111111110F4
def expm1Q2 : Float := Float.ofBits 0x3F5A01A019FE5585
def expm1Q3 : Float := Float.ofBits 0xBF14CE199EAADBB7
def expm1Q4 : Float := Float.ofBits 0x3ED0CFCA86E65239
def expm1Q5 : Float := Float.ofBits 0xBE8AFDB76E09C32D

/-- `y · 2^k` as fdlibm computes it: `k` added to the high word, the exponent field. -/
def addExpWord (y : Float) (k : Int) : Float := withHiWord y (hiWord y + k * 2 ^ 20)

/-- fdlibm's `expm1` on the reduced argument `x` (`|x| ≤ ln 2 / 2`, the original argument
`k · ln 2 + x + c`), as compiled for the reference machine: GCC fuses the products of
`R1 + h2 * R2 + h4 * R3` and of each of `Q[i] + hxs * Q[i+1]`, `3.0 - r1 * hfx`,
`6.0 - x * t`, `x * e - hxs`, `x * (e - c) - c`, `0.5 * (x - e) - 0.5` and
`one + 2.0 * (x - e)`. -/
def expm1Reduced (x c : Float) (k : Int) : Float :=
  let hfx := x * 0.5
  let hxs := x * hfx
  let r2 := fmaF false hxs expm1Q3 expm1Q2
  let r3 := fmaF false hxs expm1Q5 expm1Q4
  let h2 := hxs * hxs
  let r1 := fmaF false hxs expm1Q1 1.0
  let h4 := h2 * h2
  let r1 := fmaF false h4 r3 (fmaF false h2 r2 r1)
  let t := fmaF false (-r1) hfx 3.0
  let e := (r1 - t) / fmaF false (-x) t 6.0 * hxs
  if k == 0 then x - fmaF false e x (-hxs) else
  let e := fmaF false (e - c) x (-c) - hxs
  if k == -1 then fmaF false 0.5 (x - e) (-0.5)
  else if k == 1 then
    if ltF x (-0.25) then (e - (x + 0.5)) * -2.0 else fmaF false (x - e) 2.0 1.0
  else if k ≤ -2 || 56 < k then addExpWord (1.0 - (e - x)) k - 1.0
  else if k < 20 then
    -- `1 - 2^-k`
    let t := Float.ofBits (UInt64.ofNat ((0x3FF00000 - 0x200000 / 2 ^ k.toNat) * 2 ^ 32))
    addExpWord (t - (e - x)) k
  else
    -- `2^-k`
    let t := Float.ofBits (UInt64.ofNat ((0x3FF - k).toNat * 2 ^ 52))
    addExpWord (x - (e + t) + 1.0) k

/-- glibc 2.43's `expm1(x)` (fdlibm's, `sysdeps/ieee754/dbl-64/s_expm1.c`), as compiled for the
reference machine: `e^x - 1` from `x = k · ln 2 + r`, `k` the integer part of `x / ln 2 ± 1/2`
(`k = ±1` from `ln 2` itself between `ln 2 / 2` and `3 ln 2 / 2`), and a rational approximation
on `r`; `x` itself below `2^-54`, `-1` below `-56 ln 2`, `+∞` above `ln DBL_MAX`. -/
def expm1F (x : Float) : Float :=
  let hx := hiWord x
  let ix := hx % 2 ^ 31
  let neg := decide (2 ^ 31 ≤ hx)
  let general (s : Float) : Float :=
    let k := match decodeF (s + x * invLn2) with
      | .finite n m e => truncVal n m e
      | _ => 0
    let t := intToF k
    let hi := fmaF false (-t) ln2Hi x
    let lo := t * ln2Lo
    let r := hi - lo
    expm1Reduced r (hi - r - lo) k
  if 0x40436879 < ix then
    if 0x7FEFFFFF < ix then (if isNaNF x then x + x else if neg then -1.0 else x)
    else if 0x40862E41 < ix && ltF expm1Over x then infF false
    else if neg then expm1Tiny - 1.0
    else general 0.5
  else if 0x3FD62E42 < ix then
    if ix ≤ 0x3FF0A2B1 then
      let (hi, lo, k) := if neg then (x + ln2Hi, -ln2Lo, -1) else (x - ln2Hi, ln2Lo, 1)
      let r := hi - lo
      expm1Reduced r (hi - r - lo) k
    else general (if neg then -0.5 else 0.5)
  else if ix ≤ 0x3C8FFFFF then x
  else expm1Reduced x 0 0

/-! ### `log1p` -/

/-- The coefficients `Lp1` to `Lp7` of fdlibm's `log1p`. -/
def log1pLp1 : Float := Float.ofBits 0x3FE5555555555593
def log1pLp2 : Float := Float.ofBits 0x3FD999999997FA04
def log1pLp3 : Float := Float.ofBits 0x3FD2492494229359
def log1pLp4 : Float := Float.ofBits 0x3FCC71C51D8E78AF
def log1pLp5 : Float := Float.ofBits 0x3FC7466496CB03DE
def log1pLp6 : Float := Float.ofBits 0x3FC39A09D078C69F
def log1pLp7 : Float := Float.ofBits 0x3FC2F112DF3E5244

/-- `0.66666666666666666` of fdlibm's `log1p`, the double nearest to `2/3`. -/
def twoThirds : Float := Float.ofBits 0x3FE5555555555555

/-- fdlibm's `log1p` from `1 + x = 2^k · (1 + f)` (`√2/2 ≤ 1 + f < √2`), `c` the rounding error
of `1 + x` divided by it, `hu` the normalized high word's fraction bits (0: `|f| < 2^-20`), as
compiled for the reference machine: GCC fuses `R1 + z2 * R2` (through `R1 = z * Lp1`), the
products into `z4 * R3`, `z6 * R4` and each of `Lp[i] + z * Lp[i+1]`, and every `k * ln2_hi`
and `k * ln2_lo` into its sum. -/
def log1pReduced (f c : Float) (k : Int) (hu : Nat) : Float :=
  let hfsq := f * 0.5 * f
  let kf := intToF k
  if hu == 0 then
    if eqF f 0 then
      if k == 0 then 0.0 else fmaF false kf ln2Hi (fmaF false kf ln2Lo c)
    else
      let r := fmaF false (-f) twoThirds 1.0 * hfsq
      if k == 0 then f - r else fmaF false kf ln2Hi (-(r - fmaF false kf ln2Lo c - f))
  else
    let s := f / (f + 2.0)
    let z := s * s
    let r2 := fmaF false z log1pLp3 log1pLp2
    let r4 := fmaF false z log1pLp7 log1pLp6
    let r3 := fmaF false z log1pLp5 log1pLp4
    let z2 := z * z
    let r2z2 := r2 * z2
    let z4 := z2 * z2
    let a := fmaF false z log1pLp1 r2z2
    let z6 := z2 * z4
    let r := fmaF false z6 r4 (fmaF false z4 r3 a)
    let w := (r + hfsq) * s
    if k == 0 then f - (hfsq - w)
    else fmaF false kf ln2Hi (-(hfsq - (fmaF false kf ln2Lo c + w) - f))

/-- glibc 2.43's `log1p(x)` (fdlibm's, `sysdeps/ieee754/dbl-64/s_log1p.c`), as compiled for the
reference machine: `x` below `2^-54`, `x - x²/2` below `2^-29`, `f = x` between `-0.2929` and
`0.41422`, else `1 + x` (`x` itself from `2^53`) split into `2^k · (1 + f)` with a correction
term; `-∞` at `-1`, NaN below. -/
def log1pF (x : Float) : Float :=
  let hx := hiWordInt x
  let ax := hiWord x % 2 ^ 31
  let normalize (u c : Float) : Float :=
    let k : Int := (hiWord u / 2 ^ 20 : Nat) - 1023
    let hu : Nat := hiWord u % 2 ^ 20
    if hu < 0x6A09E then log1pReduced (withHiWord u (hu + 0x3FF00000) - 1.0) c k hu
    else
      log1pReduced (withHiWord u (hu + 0x3FE00000) - 1.0) c (k + 1) ((0x100000 - hu) / 4)
  let viaU : Float :=
    if hx < 0x43400000 then
      let u := x + 1.0
      let k : Int := (hiWord u / 2 ^ 20 : Nat) - 1023
      normalize u ((if 0 < k then 1.0 - (u - x) else x - (u - 1.0)) / u)
    else normalize x 0.0
  if hx < 0x3FDA827A then
    if 0x3FF00000 ≤ ax then (if eqF x (-1.0) then infF true else nanF)
    else if ax < 0x3E200000 then (if ax < 0x3C900000 then x else fmaF false (-(x * x)) 0.5 x)
    else if 0 < hx || hx ≤ (0xBFD2BEC3 : Int) - 2 ^ 32 then log1pReduced x 0.0 0 1
    else viaU
  else if 0x7FF00000 ≤ hx then x + x
  else viaU

end CIR.Std
