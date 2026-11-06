# complex: complex numbers

## The type, its operations and constants

`!cir.complex<T>` is parsed as the type `T[2]`, real part first: C11 6.2.5p13 gives a complex type the
representation and alignment of an array of two elements of its real type. Complex objects are arrays in memory
(locals, globals, struct members, arrays of them, pointers into them, `memcpy`), and a complex value is
`.arr [re, im]`, loaded, stored, passed and returned like other aggregate values.

| CIR | semantics |
| --- | --- |
| `cir.complex.create %re, %im` | `Op.complexCreate`: `.arr [re, im]` |
| `cir.complex.real`, `cir.complex.imag` | `Op.complexPart`: a part; of a real operand (Clang's form of `__real__ x`, `__imag__ x`), the value itself and 0 |
| `cir.complex.real_ptr`, `cir.complex.imag_ptr` | `getMember` 0 and 1: the addresses of the elements |
| `cir.complex.add`, `sub`, `fadd`, `fsub` | `Op.complexArith`: part by part; integer parts wrap (Clang's code for complex integers carries no overflow flags), floating parts IEEE (`float` rounded to binary32) |
| `cir.cmp eq`, `ne` of complex values | `Op.complexEq`: equal when the real parts and the imaginary parts are (C11 6.5.9p4: `-0 == +0`, a NaN part unequal) |
| `#cir.const_complex<re, im>` | the constant array of the two parts; `#cir.zero` of a complex type is zero-initialisation of `T[2]` |

Clang's CIR (this toolchain) spells everything else with scalar operations on the parts: negation, the conjugate
(`~`), conversions between complex types and from or to real types and `bool`, integer multiplication and
division, and floating multiplication, which it computes inline and hands to `__muldc3` only when both parts come
out NaN. Floating division calls the runtime library (`__divdc3`, `__divsc3`).

## The runtime library's multiplication and division

`Model.mulc3` and `Model.divc3` model `__muldc3`, `__divdc3` and their `float` versions `__mulsc3`, `__divsc3`
(recognized by name and signature; `CIR/Std/Complex.lean`), as libgcc computes them, the library native programs
link here (GCC 15.2's `libgcc2.c`):

* multiplication: `(ac - bd) + i(ad + bc)`; when both parts are NaN, Annex G's recovery of infinities (an infinite
  factor's parts boxed to ±1 / ±0 and the other factor's NaNs made zeros, or after an overflow every NaN made a
  zero), then `∞ · (ac - bd)`, `∞ · (ad + bc)`;
* `double` division: Smith's method with McGehearty's scaling (GCC 12 and later): halved when the larger part of
  the divisor is at least `DBL_MAX / 2`, multiplied by `2^52` when it is below `DBL_EPSILON` or a part of the
  dividend is subnormal, the other order of computation for a subnormal ratio; then, when both parts are NaN, the
  infinities and zeros of nonzero / zero, infinite / finite and finite / infinite;
* `float` division: in `double` by the textbook formula (the products of `float`s are exact), each part rounded to
  `float`, then the same recovery in `float`.

The reference machine's libgcc (<os-image>'s GCC 15.2, `libgcc.a` and `libgcc_s.so.1`) is compiled for x86-64-v3 with
GCC's default `-ffp-contract=fast`, so its object code fuses products into sums: in `__divdc3`, `c · ratio + d`,
`a · ratio + b`, `b · ratio - a` and the other order's are single fused multiply-adds, and each recovery fuses
one product of each sum (read from the disassembly; the main computation of the multiplications is unfused).
The model fuses the same ones (`Std.fmaF`: `x · y + z` rounded once, from the exact rational value). Without
them two of the test divisions come out differently in the last bit. A libgcc built for baseline x86-64 has no
fused operations; compiler-rt multiplies the same way but divides by another method (scaling by `logb` /
`scalbn`).

Lean's `Float` has a single NaN, without a sign. Where libgcc copies a NaN's sign bit into a zero (the boxing
`copysign(0, NaN)`), the model's zero is +0: that shows only as the sign of a zero part of a few recovered results
(three labelled cases). `__mulxc3` and `__divxc3` (`long double`) have no model.

## Narrowings

None. A `cir.cmp` whose operand type is `T[2]` is now a complex comparison: CIR compares no arrays.

## Test labels changed

None in the existing case files. New: `tests/difftest/complex.cpp` (`CASES=complex_cases.txt`, every case
labelled).
