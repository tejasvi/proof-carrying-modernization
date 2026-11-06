# memb: memcpy, memmove and memset over bytes

`memcpy`, `memmove` and `memset` copy and set bytes (C11 7.24.2.1p2, 7.24.2.2p2, 7.24.6.1p2). Between
objects of different types, or over part of an object, they were UB "byte-level access not modelled"
(rog's core audit: `r_memcpy_struct_other`, `y_memcpy_into_struct`, `y_memcpy_into_member`,
`y_memset_member_span`, `b_memset_ones`). Now these copies move the bytes of the objects' representations
(6.2.6.1p4, little-endian), in the smallest object along the pointer's path that contains the range: the
scalars the range reaches are read as bytes (`Std.scalarBytes`, phase 1's `byteOf`) and rebuilt from bytes
(`Std.scalarOfBytes`), the others are kept. Whole objects of one type (and integers of one width) are copied
as values as before, and `memset` of zero or of a char range is unchanged: only the former UB cases take the
byte path (`Std.memcpyBytes`, `Std.memsetBytes`).

Rules kept: an indeterminate source byte leaves its scalar indeterminate (a read of it is UB), as does a
partly written indeterminate scalar (phase 1); `memcpy` between overlapping bytes is UB (`Std.bytesOverlap`
when the ranges are not typed ranges); a pointer is rebuilt only from all its bytes, in order, within one
copy (zero bytes give the null pointer), otherwise the target is indeterminate (UB on use); a `bool` byte
other than 0 / 1 and a NaN bit pattern give an indeterminate value; bytes of implicit padding are
indeterminate and not stored. A range that goes into a union member, or covers a union, stays UB "byte-level
access not modelled" (a member's slot can hold a stale value).

## Narrowings

None: no statement changed. `WF_memsetBytes` and `WF_memcpyBytes` join `WF_memsetModel` and
`WF_memcpyModel` (`cir_wf_auto` rules).

## Test labels changed

None in the existing case files (cirrun's output identical to fa199c7's). New: `tests/difftest/memb.cpp`
(`CASES=memb_cases.txt`, every case labelled).

## Gaps (labelled UB in memb_cases.txt)

Defined or unspecified in C, UB in the model: a pointer through a char buffer (`u_ptr_via_bytes`; pointer
bytes have no values here, so they cannot be stored in a char object), a pointer's bytes into a `long`
(`u_ptr_to_long`), half of an uninitialized `int` written (`u_uninit_partial`), a NaN made by `memset`
(`u_memset_nan`; as phase 1, a NaN's bytes are not modelled), a padding byte read after `memset` and member
stores (`u_padding_byte`; implicit padding has no storage), and a union's bytes (`u_union_bytes`).
