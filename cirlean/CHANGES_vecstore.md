# vecstore: vector accesses through pointers to objects of other types, vector members' layout and alignment

- A store of a vector value through a pointer to an element of a `float` array (m19, intptr/micro, found by
  cjlemmas: `*(v4flt *)(float *)(char *)buf = w`) wrote the whole vector over `buf[0]` and left `buf[1..3]`
  alone, so `buf[1]` still read 0: a silent wrong value. A vector type is `T[N]` in the model
  (`!cir.vector<N x T>`, also `!cir.complex<T>` as `T[2]`), and `Ctx.reachIn` had no rule for an access of
  an array type, so the access at a `float` object was the ordinary one (`storeTy` of the whole array value
  at that path). A load read the `float` as the vector ("expected a vector"). The pointer conversions were
  not involved: a bitcast to a pointer to an array type keeps the pointer.
- An access of an array type at an object of another type, or through a byte view, now reads or writes the
  objects at its bytes element by element (`Reach.spread`, which records already used, now with a type:
  `Ctx.spreadLoad` / `Ctx.spreadStore` over `gatherAt` / `scatterAt`): each element is an access of its type
  to the scalar at its byte (`reachScalar`), so a vector over the elements of a `T` array, over a structure
  of `T` members, or over heap storage typed as `T`s is those objects; an element at a byte where no object
  of a compatible type starts (a misaligned pointer, an `int` member under a `float` vector, C11 6.5p7), or
  past the end of the complete object, is undefined ("type-punned access"), as is an indeterminate element of
  a load. An access of an array type at an object of that type stays the ordinary one.
- At an object whose type the block's type does not give (an element of a library container, `.vel`), an
  access of an aggregate type over a value of another shape (a scalar element) is undefined
  ("type-punned access") instead of overwriting the element with the aggregate.
- Records with vector members had the wrong layout, another silent wrong value: `!cir.vector<N x T>` is
  `T[N]`, aligned as `T`, but CIR's record types hold no padding member for a vector, as LLVM aligns a
  vector to its size rounded up to a power of two (a `vector_size(N)` type is aligned to N on x86-64, GCC and
  Clang alike). `struct { float x; v4sf v; }` put `v` at byte 4 instead of 16 (size 20 instead of 32), so the
  bytes of the record read the wrong members (a `float` read through the record's bytes 16..19 gave `v[3]`
  instead of `v[0]`), differences of pointers into it gave the wrong offsets, and a `memcpy` of `sizeof`
  bytes was a false "byte-level access not modelled". The parser records each vector member's alignment
  (`RecordDecl.vecAligns`, from the member's spelling: a vector, or an array of vectors; printed by cir2lean
  only when not empty), and `Ctx.sizeAlign` and `Ctx.memberOffsets` align those members by it (`v` at 16,
  `struct { float x; v8sf v; }` at 32, `struct { char c; v2sf v; }` at 8; a structure or union holding one is
  aligned accordingly).
- A vector access through a pointer aligned for the element but not for the vector (`*(v4sf *)&buf[1]`) was
  executed, element by element, though C leaves the conversion that made the pointer undefined (6.3.2.3p7),
  C++ leaves its value unspecified, and natively the access is an aligned vector move that faults. CIR states
  the access's alignment (`cir.load align(16)`, `cir.store align(16)`): the parser puts an `Op.alignCheck`
  before a load or a store of a vector type whose stated alignment exceeds its element's, which is undefined
  ("misaligned vector access") unless the pointer's byte position in its complete object is a multiple of it
  (`Ctx.posAligned`, a position not known counting as aligned), in C and C++. The conversion itself is not
  checked: CIR's types do not show a typedef's alignment, so a pointer to `v4sf` and a pointer to a vector
  typedef aligned as its element (`vector_size(16), aligned(4)`, whose accesses state `align(4)` and are
  defined at any float) look alike there; a misaligned conversion whose pointer is never used is missed. A
  three-element vector is not padded to four.

## Narrowings

- An aggregate access over a library container's scalar element (for example `*(v4sf *)v.data()` of a
  `std::vector<float>`) is UB (it overwrote or misread the element).
- A vector load or store with a stated alignment above its element's, through a pointer not aligned to it, is
  UB (it read or wrote the elements).

## Test labels changed

None in the existing case files. New: `tests/difftest/vecstore.c` (a C source) and `vecstorex.cpp` (C++: the
vector alignment and the library container gaps), `CASES=vecstore_cases.txt`, every case labelled.
