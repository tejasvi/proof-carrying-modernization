import CIR.Std.Float

/-!
  Complex multiplication and division of the C runtime library: `__muldc3`, `__divdc3` and the
  `float` versions `__mulsc3`, `__divsc3`, which Clang and GCC call for `*` and `/` of complex
  floating types (C11 Annex G.5.1; Clang's CIR multiplies inline and calls `__muldc3` only when
  both parts came out NaN).

  They compute what libgcc computes, the library native programs link here (GCC 15's
  `libgcc2.c`): the product of Annex G's example (G.5.1p8) with its recovery of infinities that
  came out as NaN + iNaN; the quotient by Smith's method with McGehearty's scaling (GCC 12 and
  later), then the recovery of infinities and zeros; a `float` quotient in `double` by the
  textbook formula (the target has double-precision hardware). Each operation is IEEE binary64,
  or binary32 for `float` (`roundSingle` of the exact double result: correct for `+ - * /` of
  `float`s), in the order of the reference machine's libgcc, which GCC compiled with fused
  multiply-adds (`fmaF`: `-ffp-contract=fast`, an x86-64-v3 build): where its code fuses a
  product into a sum, so does the model. compiler-rt multiplies the same way but divides by
  another method (scaling by `logb` / `scalbn`).
-/

namespace CIR.Std

/-- `|x|`: `x` with its sign bit cleared. -/
def fabsF (x : Float) : Float := Float.ofBits (x.toBits &&& 0x7FFFFFFFFFFFFFFF)

/-- `copysign(x, y)`: the magnitude of `x` with the sign bit of `y` (a NaN's sign bit too). -/
def copysignF (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

def isNaNF (x : Float) : Bool := decodeF x == .nan

def isInfF (x : Float) : Bool :=
  match decodeF x with
  | .inf _ => true
  | _ => false

def isFiniteF (x : Float) : Bool :=
  match decodeF x with
  | .finite .. => true
  | _ => false

/-- `x < y`, false when either is a NaN. -/
def ltF (x y : Float) : Bool :=
  match fkey (decodeF x), fkey (decodeF y) with
  | some a, some b => decide (a < b)
  | _, _ => false

/-- `x ≤ y`, false when either is a NaN. -/
def leF (x y : Float) : Bool :=
  match fkey (decodeF x), fkey (decodeF y) with
  | some a, some b => decide (a ≤ b)
  | _, _ => false

/-- `x == y` (`-0 == +0`), false when either is a NaN. -/
def eqF (x y : Float) : Bool :=
  match fkey (decodeF x), fkey (decodeF y) with
  | some a, some b => a == b
  | _, _ => false

/-- `x · y + z` rounded once (IEEE 754 fusedMultiplyAdd, to nearest, ties to even), to binary64,
or to binary32 when `single` (then `x`, `y`, `z` are `float`s, held as doubles). A NaN operand,
`∞ · 0` and `∞ - ∞` give the NaN; an exact zero is `-0` only as the sum of two negative zeros. -/
def fmaF (single : Bool) (x y z : Float) : Float :=
  let rnd (neg : Bool) (num den : Nat) : Float :=
    if single then ratToSingle neg num den else ratToFloat neg num den
  -- an infinite product of sign `neg`, plus `z`
  let infPlus (neg : Bool) : Float :=
    match decodeF z with
    | .nan => nanF
    | .inf sz => if sz == neg then infF neg else nanF
    | .finite .. => infF neg
  match decodeF x, decodeF y, decodeF z with
  | .nan, _, _ => nanF
  | _, .nan, _ => nanF
  | .inf sx, .inf sy, _ => infPlus (sx != sy)
  | .inf sx, .finite sy my _, _ => if my = 0 then nanF else infPlus (sx != sy)
  | .finite sx mx _, .inf sy, _ => if mx = 0 then nanF else infPlus (sx != sy)
  | .finite _ _ _, .finite _ _ _, .nan => nanF
  | .finite _ _ _, .finite _ _ _, .inf sz => infF sz
  | .finite sx mx ex, .finite sy my ey, .finite sz mz ez =>
    let sp := sx != sy
    -- both addends as integer multiples of `2^e0`
    let e0 := min (ex + ey) ez
    let p : Int := (mx * my * 2 ^ (ex + ey - e0).toNat : Nat)
    let q : Int := (mz * 2 ^ (ez - e0).toNat : Nat)
    let s := (if sp then -p else p) + (if sz then -q else q)
    if s = 0 then rnd (sp && sz && mx * my == 0 && mz == 0) 0 1
    else if 0 ≤ e0 then rnd (decide (s < 0)) (s.natAbs * 2 ^ e0.toNat) 1
    else rnd (decide (s < 0)) s.natAbs (2 ^ (-e0).toNat)

/-- Annex G's "box" of a factor's part: `±1` for an infinity, `±0` otherwise, with its sign. -/
def boxF (x : Float) : Float := copysignF (if isInfF x then 1 else 0) x

/-- A NaN changed to a zero of its sign; any other value unchanged. -/
def nanToZeroF (x : Float) : Float := if isNaNF x then copysignF 0 x else x

/-- `__muldc3(a, b, c, d)`, or `__mulsc3` when `single`: `(a + ib) · (c + id)` as
`(ac - bd) + i(ad + bc)`; when both parts are NaN, the infinities are recovered (an infinite
factor's parts boxed, the other factor's NaNs made zeros, or, after an overflow, every NaN made a
zero) and the parts are `∞ · (ac - bd)`, `∞ · (ad + bc)` again, each sum with one product fused. -/
def mulc3 (single : Bool) (a b c d : Float) : Float × Float :=
  let r (f : Float) : Float := if single then roundSingle f else f
  let ac := r (a * c)
  let bd := r (b * d)
  let ad := r (a * d)
  let bc := r (b * c)
  let x := r (ac - bd)
  let y := r (ad + bc)
  if !(isNaNF x && isNaNF y) then (x, y) else
  -- z = a + ib is infinite
  let zInf := isInfF a || isInfF b
  let (a, b, c, d) := if zInf then (boxF a, boxF b, nanToZeroF c, nanToZeroF d) else (a, b, c, d)
  -- w = c + id is infinite
  let wInf := isInfF c || isInfF d
  let (a, b, c, d) := if wInf then (nanToZeroF a, nanToZeroF b, boxF c, boxF d) else (a, b, c, d)
  -- an overflow
  let ovf := !zInf && !wInf && (isInfF ac || isInfF bd || isInfF ad || isInfF bc)
  let (a, b, c, d) :=
    if ovf then (nanToZeroF a, nanToZeroF b, nanToZeroF c, nanToZeroF d) else (a, b, c, d)
  if zInf || wInf || ovf then
    let inf := infF false
    (r (fmaF single a c (-(r (b * d))) * inf), r (fmaF single a d (r (b * c)) * inf))
  else (x, y)

/-- `__divdc3(a, b, c, d)`: `(a + ib) / (c + id)` by Smith's method, the operands first scaled
by powers of 2 against overflow and underflow (halved when the larger part of the divisor is at
least `DBL_MAX / 2`, multiplied by `2^52` when it is below `DBL_EPSILON` or when a part of the
dividend is subnormal); then, when both parts are NaN, the infinities and zeros of
nonzero / zero, infinite / finite and finite / infinite. -/
def divdc3 (a b c d : Float) : Float × Float :=
  let rbig := Float.ofBits 0x7FDFFFFFFFFFFFFF      -- DBL_MAX / 2
  let rmin := Float.ofBits 0x0010000000000000      -- DBL_MIN
  let rmin2 := Float.ofBits 0x3CB0000000000000     -- DBL_EPSILON
  let rminscal := Float.ofBits 0x4330000000000000  -- 1 / DBL_EPSILON
  let rmax2 := Float.ofBits 0x7C9FFFFFFFFFFFFF     -- DBL_MAX / 2 · DBL_EPSILON
  let half := Float.ofBits 0x3FE0000000000000
  let fma := fmaF false
  -- `m` is the larger part of the divisor (`|d|` in the first case, `|c|` in the second)
  let scale (a b c d m : Float) : Float × Float × Float × Float :=
    let (a, b, c, d) := if leF rbig (fabsF m) then (a * half, b * half, c * half, d * half)
      else (a, b, c, d)
    let m := if leF rbig (fabsF m) then m * half else m
    if ltF (fabsF m) rmin2
        || (ltF (fabsF a) rmin && ltF (fabsF b) rmax2 && ltF (fabsF m) rmax2)
        || (ltF (fabsF b) rmin && ltF (fabsF a) rmax2 && ltF (fabsF m) rmax2) then
      (a * rminscal, b * rminscal, c * rminscal, d * rminscal)
    else (a, b, c, d)
  let (a, b, c, d, x, y) :=
    if ltF (fabsF c) (fabsF d) then
      let (a, b, c, d) := scale a b c d d
      let ratio := c / d
      let denom := fma c ratio d
      if ltF rmin (fabsF ratio) then (a, b, c, d, fma a ratio b / denom, fma ratio b (-a) / denom)
      else (a, b, c, d, fma (a / d) c b / denom, fma (b / d) c (-a) / denom)
    else
      let (a, b, c, d) := scale a b c d c
      let ratio := d / c
      let denom := fma d ratio c
      if ltF rmin (fabsF ratio) then (a, b, c, d, fma b ratio a / denom, fma (-a) ratio b / denom)
      else (a, b, c, d, fma (b / c) d a / denom, fma (-(a / c)) d b / denom)
  if !(isNaNF x && isNaNF y) then (x, y)
  else if eqF c 0 && eqF d 0 && (!isNaNF a || !isNaNF b) then
    (copysignF (infF false) c * a, copysignF (infF false) c * b)
  else if (isInfF a || isInfF b) && isFiniteF c && isFiniteF d then
    let (a, b) := (boxF a, boxF b)
    (fma c a (d * b) * infF false, fma b c (-(d * a)) * infF false)
  else if (isInfF c || isInfF d) && isFiniteF a && isFiniteF b then
    let (c, d) := (boxF c, boxF d)
    (fma a c (b * d) * 0, fma b c (-(a * d)) * 0)
  else (x, y)

/-- `__divsc3(a, b, c, d)`: `float` division, computed in `double` as
`((ac + bd) + i(bc - ad)) / (c² + d²)` (exact products of `float`s), each part rounded to `float`;
then the recovery of `divdc3`, in `float`. -/
def divsc3 (a b c d : Float) : Float × Float :=
  let fma := fmaF false
  let denom := fma c c (d * d)
  let x := roundSingle (fma a c (b * d) / denom)
  let y := roundSingle (fma b c (-(a * d)) / denom)
  if !(isNaNF x && isNaNF y) then (x, y) else
  let r := roundSingle
  let fmas := fmaF true
  if eqF c 0 && eqF d 0 && (!isNaNF a || !isNaNF b) then
    (r (copysignF (infF false) c * a), r (copysignF (infF false) c * b))
  else if (isInfF a || isInfF b) && isFiniteF c && isFiniteF d then
    let (a, b) := (boxF a, boxF b)
    (r (fmas c a (r (d * b)) * infF false), r (fmas b c (-(r (d * a))) * infF false))
  else if (isInfF c || isInfF d) && isFiniteF a && isFiniteF b then
    let (c, d) := (boxF c, boxF d)
    (r (fmas a c (r (b * d)) * 0), r (fmas b c (-(r (a * d))) * 0))
  else (x, y)

end CIR.Std
