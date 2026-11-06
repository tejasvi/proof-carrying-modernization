# vecscalar: bitcasts between a vector and a scalar

A `cir.cast bitcast` between a vector and a scalar of its size (`(long long)v2si`, `(v4si)x` of an `__int128`,
`(unsigned)v4qu`, `(v2sf)` of a `long long`) reinterprets the value's bytes, little-endian, exactly as a bitcast
between vector types does (`reinterpretVals`, with `byteOf` / `setByte`): integers exactly; undefined for
different sizes.

NaNs element by element (rog's V1): a bitcast whose result has an element with a NaN's bit pattern, or whose
bytes come from a NaN or an indeterminate value (`Float` has a single NaN, so a NaN's bytes are not kept), was
UB for the whole cast; that element is now indeterminate (`.undef`), the others exact, so only a use of it is
undefined. `{0x7fc00001, 0x3f800000}` cast to two floats reads its second element.
GCC's manual (Using Vector Instructions through Built-in Functions): "It is possible to cast from one vector type to
another, provided they are of the same size (in fact, you can also cast vectors to and from other data types of
the same size)." GCC and Clang take only integer scalars there. It is a conversion of values, not an access to
memory, so the byte-view rule (through a byte view only a character access is defined) is not involved.

The cast case of `evalSimple` now calls `castVal`, which holds the vector cases (`vecCast` between vectors,
`vecToScalar` / `scalarToVec` between a vector and a scalar) and `evalCast` for the others: inline, the
automatic proof of `WF_evalSimple` ran out of heartbeats. `castVal` is in the `cir_exec` simp set, so that the
VCG's scalar casts still reach `evalCast` (the Examples and the CJ examples build unchanged).

A pointer to a vector converted to a pointer to its element type (`(int *)&v`) designates element 0 and its strides
count the vector's elements, by bytes' rule for array objects (`CHANGES_bytes.md`, 2 and 3): `vec_cases`'
`g_int_ptr` gap is `t_int_ptr`, reads, writes and the one-past pointer, expected MATCH, and `u_int_ptr_past` reads
one past the last element, expected UB.

README: the vector bullet, with GCC's sentence; the complex row says the model follows the installed libgcc
(x86-64-v3, fused products) and differs from compiler-rt.

## Narrowings

None.

## Test labels changed

`vec_cases.txt`: `g_int_ptr 0` and `g_int_ptr 2` (UB, a gap) are now `t_int_ptr` with seven cases, expected
MATCH; new: `u_int_ptr_past` (UB), `t_scalar_cast` 0-8 and `t_nan_lanes` 0-2 (MATCH), `g_nan_cast` (UB, the NaN
gap: a NaN element made by a bitcast, then read).
