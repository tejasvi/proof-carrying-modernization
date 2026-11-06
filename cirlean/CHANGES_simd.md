# simd: vectors

## The type, its operations and constants

`!cir.vector<N x T>` (GNU `vector_size`) is parsed as the type `T[N]`, like a complex
type (`CHANGES_complex.md`): vector objects are arrays in memory and a vector value is `.arr xs`.

| CIR | semantics |
| --- | --- |
| `#cir.const_vector<[...]>` | the constant array of the elements; `#cir.zero` of a vector type is zero-initialisation of `T[N]` |
| `cir.vec.create(%a, %b, ...)` | `Op.vecCreate`: the elements in order |
| `cir.vec.splat %x` | `Op.vecSplat`: `N` copies of `x` |
| `cir.vec.extract %v[%i]`, `cir.vec.insert %x, %v[%i]` | `Op.vecExtract`, `Op.vecInsert`: undefined at an index outside the vector |
| `cir.vec.cmp(k, %a, %b)` | `Op.vecCmp`: element by element, -1 where the comparison holds and 0 where it does not, in the result's element type (IEEE for floats: a NaN element is unordered) |
| `cir.vec.shuffle(%a, %b) [i, ...]` | `Op.vecShuffle`: element `i` of `a` then `b` for each index; -1 gives an indeterminate element (a use of it is undefined) |
| `cir.vec.ternary(%c, %a, %b)` | `Op.vecTernary`: element by element, `a`'s where `c`'s is nonzero, else `b`'s |

The integer and bool operations (`binop`), floating operations (`fbinop`), `cir.fmuladd` (unfused, as for
scalars), shifts, unary operations, `cir.fneg` and casts of a vector type act element by element. Integer elements
wrap: Clang emits vector arithmetic without overflow flags. A division or remainder by a zero element and a shift
out of range are undefined, as for scalars. A `bitcast` between vector types reinterprets the elements' bytes,
little-endian (`byteOf`, `setByte`): integers exactly, `float` and `double` elements unless a NaN's bit pattern is
involved (`Float` has a single NaN).

Not modelled (each UB, so a proof that reaches one fails): the target's intrinsics (`cir.call_llvm_intrinsic`).
Bitcasts between a vector and a scalar, and the elements of a vector through a pointer to its element type, came
with vecscalar (`CHANGES_vecscalar.md`).

## Narrowings

None.

## Test labels changed

None in the existing case files. New: `tests/difftest/vec.cpp` (`CASES=vec_cases.txt`, every case labelled).
