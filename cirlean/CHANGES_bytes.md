# bytes: the bytes of objects, pointer arithmetic in the pointer's units, the scalars aggregates start with

Changes at the C level:

1. An access through a character type (`char`, `signed char`, `unsigned char`, `std::byte`) to an integer,
   floating or `bool` object reads or writes a byte of its representation (C11 6.5p7, last bullet;
   6.2.6.1p4), little-endian; it was UB "type-punned access". The bytes of a record are those of its
   members, by their offsets. Pointer bytes, the bytes of a NaN the program computed, a byte written into an
   indeterminate object, padding bytes and bytes outside the object are UB. A character store, or a
   `memcpy` / `memmove` / `memset` that goes byte by byte (`scalarOfBytes`), that leaves a `_Bool` or
   floating object with bytes that are no value of its type (a `_Bool` byte other than 0 or 1, a NaN's bit
   pattern) leaves them there (6.2.6.1p5; `setByteRepr`, the object holds its bytes as an `.int`):
   character reads and copies give them back, a store that makes a value again gives that value, and only a
   read of the object as its type is UB ("read of a bool whose byte is neither 0 nor 1"), or for a NaN not
   modelled. Such a store was UB "byte access not modelled", and such a copy left the object indeterminate:
   a `_Bool`'s byte set to 2 and back to 0, a double copied byte by byte last byte first (NaN bits for some
   steps; soundness audit of next3, F8, F9), a double's bytes set to 0xff by `memset` and read back.
2. `cir.ptr_stride` / `cir.ptr_diff` count objects of the pointer's type (C11 6.5.6p8, p9): a stride by `n`
   on a pointer to `T` moves `n * sizeof T` bytes. They counted the elements of the array the pointer was in
   whatever its type, so `*(int *)((char *)a + 4)` read `a[4]` instead of `a[1]` (a wrong defined value).
   When the pointer designates an array element of the size of `T`, the result is the same as before.
   Otherwise, for a character type, the arithmetic is in bytes over the block's complete object (6.2.6.1p4,
   6.3.2.3p7): `(char *)&s.b - (char *)&s` is `b`'s offset and `container_of` gives the containing object.
   For another type it is read strictly (6.5.6p7, p8): the object of `T`'s size that the pointer designates
   (a structure's first member, an array object's element 0) moves within its array if it is an array
   element (a pointer to an array object converted to a pointer to its element type counts the array's
   elements: `std::initializer_list` keeps its backing array so), else within an array of one, the object
   and one past it: `&x + 1` and a single heap `T` plus 1 are one past, `&s.a + 1` cannot be dereferenced
   even at `s.b`'s address, `&s.a + 2` is UB, and `(int *)s + 1` over an array of two-`int` structures is
   one past `s[0].x`. A stride in other units than an array's elements (`(short *)a + 2` over an `int`
   array) moves by bytes within the array, with only character accesses defined between elements. A
   relational comparison of pointers that are not array elements compares their byte positions (6.5.8p5).
3. A scalar access through a pointer to a structure, array or union reaches the scalar the object starts
   with (C11 6.7.2.1p15, p16): its first member, its element 0, a union's active member (the first that
   holds a value) or member 0, recursively. Then a compatible type is an ordinary access, a character type a
   byte of that scalar, another type UB "type-punned access". It was unchecked, and a store replaced the
   whole aggregate with the scalar: `*(unsigned char *)&s = 7; *(int *)&s` gave 7 (soundness audit of next2,
   G5); a `long long` access over two `int` members was defined.
4. An access of a record type to an object of another record type (`T t = *(T *)&s`) is UB "type-punned
   access" (6.5p7; C++ [basic.lval]p11; audit G4), unless the object starts with a subobject of that type
   (6.7.2.1p15), which it then reaches. At an array whose first element (recursively) has the type, the
   access reaches that element (a pointer to an array object used as a pointer to its element type; it
   returned the whole array). Empty classes and a class's `.base` layout are exempt.
5. A pointer converted to a pointer to a record type (`cir.cast bitcast`) designates the subobject of that
   type the object starts with, or the enclosing object of that type that it starts (6.7.2.1p15, p16):
   member accesses through `(S *)&o` reach the members of `o.in`, and `(O *)&o.in` gives `o` back. Through
   such a pointer, C++'s `S::operator=` wrote `o.z` for `o.in.b`. `cir.get_member` does the same with the
   record type of its base (`Ctx.memberBase`), so a pointer to an array of records that reaches a member
   access without a cast (`std::initializer_list` stores its backing array through a cast of the field's
   address) reaches element 0's member, not element `i` of the array.
6. Pointers into the same block compare by address (phase 3, `Ctx.ptrEq?`, `Ctx.evalCmpB`): by their byte
   positions in its complete object (C11 6.5.9p6, 6.5.8p5). A structure and its first member, an array and
   its element 0, a row and its element 0, the members of a union, one past an object and the object after
   it compare equal; equality was structural, so they compared unequal, a wrong defined value. Relational
   comparisons of pointers into different arrays of the same object (the rows of a two-dimensional array)
   follow their addresses; they were UB. Elements of one array still compare by their indices, pointers into
   different blocks stay unequal and their relational comparison UB. `cir.atomic.cmpxchg` compares pointers
   the same way.
7. 6.5p7's aggregate clause (phase 3b): a record type whose members include the types of the objects it
   covers may access them. A load or store of record type over a scalar, or over an array that does not
   start with that record type, goes member by member (`Reach.spread`, `Ctx.spreadLoad` /
   `Ctx.spreadStore`): each scalar member at its offset after the object's byte position, over the scalar
   there, as a scalar access of the member's type would be (a compatible scalar, a byte for a character
   type, else UB "type-punned access"), padding not read or written, nested records and arrays member by
   member. A member access through a pointer to a record over a scalar or an array places the member by
   bytes the same way (`Ctx.memberPath`, `Ctx.placeMember`): C++'s `P::operator=` assigns member by member.
   `*(P *)&s.a = p` with `P` a structure of two ints writes `s.a` and `s.b`; `P q = *(P *)&s.a` reads them;
   a member that falls outside the object or on no scalar of its type is UB. An access of a record type to
   an object of another record type stays UB (item 4).
8. In C, a `cir.cast bitcast` to a pointer to an object type is UB "misaligned pointer conversion" when the
   pointer is not correctly aligned for that type (C11 6.3.2.3p7), used or not (`Ctx.castCheck`,
   `Ctx.castAligned`): a complete object counts as aligned for every type, as `malloc`'s storage is, and
   the pointer's byte position in it must be a multiple of the type's alignment. `(int *)((char *)a + 1)`
   over an `int` array was a byte view whose accesses only were UB (soundness audit of next3, M11). In C++
   the value of such a pointer is unspecified ([expr.static.cast]p13), not undefined: it stays the pointer
   it was. Conversions to `void *`, character pointers and function pointers are unchanged.
9. A bit-field of a structure placed over other objects (item 7: `(struct BF *)&u` over a scalar or an
   array) has its declared type (6.5p7), not its storage unit's (`Ctx.bfPlaced?`): the access goes byte by
   byte over the unit's bytes (`Ctx.bfLoadBytes`, `Ctx.bfStoreBytes`), and each scalar it touches must have
   a type compatible with the field's, or the field a character type, else it is UB "type-punned access".
   Clang stores `struct {unsigned a:4, b:4;}` in one byte, so over a `float` or a `char` array its fields
   were character accesses (defined), and `struct {unsigned a:4, b:8;}` in two, so over an `unsigned int`
   they were UB (soundness audit of next3, B1, B2). The bit-fields of a structure object are unchanged.

Objects that the library models keep as other values (`opt`, `vec`) are accessed as before.

A character pointer into a scalar is a byte view: a last path element `PathElem.byte k` (byte 0 is the
object pointer itself). Character arithmetic gives canonical paths (`Ctx.canonByte`): the outermost
subobject that starts at the byte (`(int *)((char *)s + 4)` over `struct { int x, y; } s[4]` designates
`s[0].y`, the `offsetof` idiom; the end of an array is its one-past element, as element arithmetic gives
it), else a byte view of the innermost scalar that contains it. In a union the path continues in the
active member (the first that holds a value, as for item 3) when the byte lies inside it, else it is a
byte view of the union: `(short *)((char *)&u + 2)` designates `u.s[1]` while `u.s` is active (it was a
byte view of the union, so `*p` was UB; soundness audit of next3, F10). The pointer one past a lone
object is a byte view at its size, and a stride in other units within an array gives a byte view of the
element it falls in. Through a byte view only a character access is defined. The README states this
reading as deliberate.

## Proofs

`Ctx.typedLoad` / `Ctx.typedStore` take the new cases first (`Ctx.reach?`: a byte, an initial scalar or
member, type-punned); the simprocs `reduceTypedLoad` / `reduceTypedStore` decide that `Ctx.reach?` is
`none` (the ordinary access) before rewriting to `loadTy` / `storeTy`. The `@[csimp]` one-lookup versions
are re-proved; `WF_typedStore` covers the new cases. A specification is unaffected when its scalar accesses
are at paths of scalar type, its pointer arithmetic is on array elements in the elements' units, and its
conversions to record pointers and member accesses are through pointers to objects of that record type:
then `Ctx.reach?` is `none`, `Ctx.sameUnits` is true and `Ctx.convertPath` / `Ctx.memberPath` are the
identity, once the type at the path evaluates (the block's type must be known there: `cir.get_member` now
looks it up). Where a specification leaves a block's type open (`CJForest`'s items have the record type
`CJ.rt`, which only a printability predicate fixes), the type tests (`Ctx.reachTypeNone`,
`Ctx.memberRelated`, `Ctx.punnedMember`) are decided with the context's type facts, hypotheses named
`cirR_…` that the FH chain's run drivers state for the items of each printable list: the functions of a
block's type that symbolic execution evaluates (`Ty.atPath`, `Ctx.typeAt`, `Ctx.sizeAlign`,
`Ctx.sameArray`, `Ctx.convertPath`) are taken at the type the facts give, before their equations
(`reduceTyArg…`), and the simprocs `reduceReachTypeNone`, `reduceMemberRelated` and
`reducePunnedMember` decide a test from its definition. A function of the type of a block bound inside
the term simp visits (a lookup's `some blk`) stays folded until the block is known, so that a test
computed before its block's facts exist (an item reached through a pointer computed in the same step gets
them only after it) is decided once they are there. A block looked up through point updates is found
past the keys `omega` tells apart from it (over the context's arithmetic facts and the bounds of the
blocks of the lists whose items the keys are, `keysDistinct`); a key it cannot tell apart (the first and
the last item of a list are one block when the list has one item) is decided by cases
(`decideByUpdCases`, towards the test's ordinary outcome), for these tests and for `Ctx.reach?`. A test
left open on such a key alone stays folded until it is decided, and symbolic execution does not case on a
folded test (`isOpenIte`, `isOpenDecide`: the fallback unfolds it); any other undecided test is its
simplified definition, as before, so that the lookups of symbolic execution see what it waits on. The
facts never rewrite the symbolic state, where the closers expect `CJ.rt` (as global rewrite rules they
made parse_object's fail-path closers miss their lookups). Without all this, the item accesses of
parse_array and parse_object left `match`es on `CJ.rt` that symbolic execution split into the outcomes of
`Ctx.reach?` at every load and store (parse_array exceeded its 400M heartbeats at next3 33bed72), and a
member test unfolded before its block's facts existed left an infeasible `Ctx.memberOther` branch that
no closer finishes, explored in steps of up to 20 minutes. With them, at next3 bb7d2b1 and the FH chain
stating the type facts (a proof-script change; the bundle sources unchanged), parse_array takes 1.42
core-hours (1.89 at next3 a66fbda), parse_object 0.93 (1.14) and cJSON_Delete 97 s.
Arithmetic on a lone object (no array element) goes through `Ctx.charStride?` or `Ctx.lensStride?`,
which give the pointer itself for a zero stride, as `Mem.stride?` did. Pointer equality goes through
`Ctx.ptrEq?`, which is `Mem.ptrEq?` when a pointer is not into a block (NULL) or the
two are into different blocks, and the structural comparison for elements of one array; a relational
comparison of elements of one array is `evalCmp`'s, as before. The paths symbolic execution discards stay
folded: the simprocs decide the ordinary access and the member path from those type tests before the
definitions unfold, and `Ctx.reachSlow`, `Ctx.memberOther`, `Ctx.reachScalarAt`, `Ctx.reachRecordAt`,
`Ctx.memberSlow`, the member-wise accesses and the arithmetic in bytes are not in the `cir_exec` simp set
(with them in it, the CJ examples elaborated 20-35% slower). The alignment check of a conversion
(`Ctx.castCheck`, `Ctx.castAligned`) is decided without the module's layouts or byte positions for
`void`, function, character and `bool` targets and for a pointer to a block's start or its element 0;
otherwise it needs `Ctx.posAligned`, which is not in the set. The language (C or C++) is looked up only
for a pointer that is not aligned, since symbolic execution does not evaluate `ctx.mod.cxx`: with that
test first, CJDelete elaborated in 165 s instead of 84 s, with twice the reductions. In the cJSON the FH
bundles are built from, every conversion to a pointer type of a larger alignment converts NULL, a fresh
allocation (`cJSON_New_Item`), a local's address (`parse_number`'s `(char **)&after_end`) or a pointer of
that type with `const` cast away (`cJSON_CreateObjectReference`, `cJSON_CreateArrayReference`). The
placed bit-fields' functions are not in the set either; `WF_bfStoreBytes` extends `WF_evalSimple` to them.

## Narrowings (hypothesis added)

| Theorem | Added hypothesis | Why |
|---|---|---|
| `Examples.CJStrings.skip_bom_main` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | `buffer->content + buffer->offset` is a `char *` stride: its units depend on the size of the content's elements, which a free `tyc` leaves unknown. The content is a `char` array. |
| `Examples.CJStrings.skip_utf8_bom_spec` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | as above (it uses `skip_bom_main`) |

Conclusions are unchanged. `skip_bom_off` and `skip_bom_short` (no stride) and every other Example and
CJ example are unchanged.

## Test labels changed

`tests/difftest/recpun_cases.txt`: `r_pun_char_into_int` (two lines) and `r_pun_char_into_nested`, char
stores into an int member, are byte-0 writes now: expected MATCH (were UB). `tests/difftest/bytes_cases.txt`
labels the evidence-owner session's `d_int_over_struct` (two lines) UB: strictly, `(int *)s + 1` is one past `s[0].x`.

## Soundness audit of next2: lines changed

rog's audit files (`soundaudit_core/root/tests/difftest/audit*.cpp`), run with the cirrun of fa199c7 and of
this branch: 16 lines change, each to C's outcome, and each has a labelled case in `aggpath.cpp`. G5, wrong
values now as C: `r_bytestore_struct`, `r_bytestore_array`, `r_bytestore_nested`, `x_heap_bytestore`,
`y_union_root_collapse`, `y_row_bytestore`; G5, C's UB now UB: `r_llstore_struct`, `r_llstore_array`,
`r_atomic_llstore_struct`; G5, false UBs now as C: `r_bytestore_struct_b`, `r_intstore_struct_b`,
`y_row_intstore_then_elem`, `x_atomic_fetch_root`, `x_atomic_xchg_root`, `u_bytestore_union`; G4:
`r_copy_incompat` UB. Phase 3b (against next3 e0069df): the aggregate clause's `r_aggstore_member`,
`r_aggstore_elem` and `r_aggload_member` now as C (they were UB), with labelled cases in `aggclause.cpp`.
The other audit lines are unchanged.

## Soundness audit of next3: lines changed

rog's next3 audit files (`soundaudit_n3/root/tests/difftest`, the 39 case files `n3*` and `audit*` but
the libevent ones and `n3cxw`), run with the cirrun of next3 bb7d2b1 and of this branch: 9 lines change,
each to C's outcome, each with a labelled case. M11: `z_misaligned_conversion` UB (`ptralign.c`); F8, F9:
`z_bool_byte_2_then_0` and `z_transient_nan` defined (`byterepr.c`); F10: `z_union_member_char_offset`
defined (`unionbyte.c`); B1: `bb_bf_over_float`, `bb_bf_over_chars` and `bb_bf_store_over_float` UB, B2:
`b2_bf12_over_unsigned` and `b2_bf12_store_over_unsigned` defined (`bfplace.c`). `x_bool_via_char` (a
`_Bool` read while its byte is 2) stays UB, with the new message. The other lines are unchanged.

## Gaps

- Heap storage takes the type of its first cast, so a pool from `malloc` first cast to `char *` cannot hold
  structs: `g_heap_char_pool` in `bytes.cpp` is UB "invalid memory write" (labelled UB), although C gives
  allocated storage the effective type of what is stored in it (6.5p6). A struct member in a buffer
  declared as `char` is UB in C too (6.5p7, `u_arena_struct`); a struct-sized stride over such a buffer is
  defined and counts structs (`s_arena_stride`).
- Padding bytes read through a character type are UB (C: unspecified values).
- A character pointer at an element of a character array moves within that array (`Mem.stride?`, as
  before), not over the complete object: across the rows of a two-dimensional `char` array it is UB.
- A pointer from character arithmetic into a union is made canonical when the arithmetic happens: formed
  while no member holds a value, or another member is active, it stays a byte view of that member after a
  store activates another (`u_formed_before` in `unionbyte.c`, UB; C gives the value). A byte past the
  active member is a byte view of the union, whose bytes are not modelled (C: unspecified values).
- A complete object counts as aligned for every type (item 8): a conversion at a position that is a
  multiple of the target's alignment is defined, although a declared object of a smaller alignment (a
  `char` array) may sit at any address of its own alignment, which C leaves the result to.
- A bit-field read through a pointer to its structure type over another structure whose member there has
  the storage unit's type is that member's ordinary access, whatever the field's declared type.
- Library models that write into caller memory (`sscanf`, the end pointers of `strtol` / `strtod`) are
  unchanged.
- A record access member by member over a union (a union member of the record, or the object a union) is
  UB "aggregate access not modelled".
