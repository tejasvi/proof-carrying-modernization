import CIR.Semantics.Basic

/-!
  x86 SIMD intrinsics that Clang's CIR calls by their LLVM names (`cir.call_llvm_intrinsic "x86.…"`:
  the `__builtin_ia32_…` functions behind `<xmmintrin.h>` and `<emmintrin.h>` that have no generic
  vector form), as functions of their operands that compute what the instruction does (Intel SDM,
  vol. 2): PACKSSDW, PSLLW and PSRLW by an immediate count, MAXPS and MOVMSKPS. The parser makes
  `Op.x86Intrinsic` of the names in `x86Intrinsics` only; any other stays `Op.unknown`.
-/

namespace CIR.Std

/-- `x` saturated to the signed integers of `w` bits. -/
def satSigned (w : Nat) (x : Int) : Int :=
  if 2 ^ (w - 1) - 1 < x then 2 ^ (w - 1) - 1 else if x < -2 ^ (w - 1) then -2 ^ (w - 1) else x

/-- The elements of a vector value that holds integers only. -/
def vecInts : Val → Option (List Int)
  | .arr xs => xs.mapM fun x => match x with | .int i => some i | _ => none
  | _ => none

/-- The elements of a vector value that holds floating-point numbers only. -/
def vecFloats : Val → Option (List Float)
  | .arr xs => xs.mapM fun x => match x with | .float f => some f | _ => none
  | _ => none

/-- The intrinsic `name` of the operands `vs`, with result type `ty`; `none` for operands of another
shape and for the sign of a NaN, which `Float` does not keep (it has one NaN).
* `x86.sse2.packssdw.128` (PACKSSDW): the four 32-bit elements of each operand, the first's then the
  second's, each saturated to 16 bits;
* `x86.sse2.pslli.w`, `x86.sse2.psrli.w` (PSLLW, PSRLW): each 16-bit element shifted left, or right
  logically, by the count, an unsigned 32-bit number; a count above 15 gives zeros;
* `x86.sse.max.ps` (MAXPS): each element of the first operand where it is greater than the second's,
  else the second's, so also for a NaN in either and for two zeros of any sign;
* `x86.sse.movmsk.ps` (MOVMSKPS): bit `i` of the result is the sign of element `i`. -/
def x86Intrinsic (name : String) (vs : List Val) (ty : Ty) : Option Val :=
  match name, vs, ty with
  | "x86.sse2.packssdw.128", [a, b], .array (.int _ 16) 8 => do
    let xs ← vecInts a
    let ys ← vecInts b
    if xs.length = 4 ∧ ys.length = 4 then some (.arr ((xs ++ ys).map fun x => .int (satSigned 16 x)))
    else none
  | "x86.sse2.pslli.w", [a, .int c], .array (.int sg 16) 8 => do
    let xs ← vecInts a
    let c := c % 2 ^ 32
    if xs.length = 8 then
      some (.arr (xs.map fun x => .int (if 15 < c then 0 else wrap sg 16 (x % 2 ^ 16 * 2 ^ c.toNat))))
    else none
  | "x86.sse2.psrli.w", [a, .int c], .array (.int sg 16) 8 => do
    let xs ← vecInts a
    let c := c % 2 ^ 32
    if xs.length = 8 then
      some (.arr (xs.map fun x => .int (if 15 < c then 0 else wrap sg 16 (x % 2 ^ 16 / 2 ^ c.toNat))))
    else none
  | "x86.sse.max.ps", [a, b], .array (.float .single) 4 => do
    let xs ← vecFloats a
    let ys ← vecFloats b
    if xs.length = 4 ∧ ys.length = 4 then
      some (.arr ((xs.zip ys).map fun (x, y) => .float (if cmpFloat .gt x y then x else y)))
    else none
  | "x86.sse.movmsk.ps", [a], .int _ 32 => do
    let xs ← vecFloats a
    if xs.length = 4 ∧ xs.all (fun x => decodeF x != .nan) then
      some (.int (xs.zipIdx.map fun (x, i) =>
        if x.toBits &&& 0x8000000000000000 != 0 then (2 : Int) ^ i else 0).sum)
    else none
  | _, _, _ => none

end CIR.Std
