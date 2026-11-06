# contb3: the C++ library's own zero-length `<string.h>` calls; std::vector::assign; std::string's swap, range constructor, operator+ and compare

## The C++ library's own `memcpy`, `memmove`, `memset` and `memcmp` with length 0

C11 7.24.1p2 makes a pointer argument of these functions valid also when the length is 0, and the models check it
(`Std.validMemArg`). That precondition binds the program's calls. The implementation's own code relies on its
platform, which reads and writes nothing for a length of 0 (C2y N3322 makes such calls defined with null
pointers). libc++ relocates a vector's empty buffer and copies and compares empty ranges through null pointers:
`__uninitialized_allocator_relocate` at a vector's first growth, `std::copy` (`__constexpr_memmove`) and
`std::equal` (`__constexpr_memcmp_equal`) of empty ranges. Census mains graph_is_graph_bipartite and
graph_lowest_common_ancestor stopped at "memcpy: invalid pointer argument, also with length 0".

The frontend tags these calls (`Frontend.tagStdMemCalls`, after the models are attached and aliases resolved). In
the body of a function of the C++ standard library (`Frontend.isStdLibFunc`: its demangled name is in namespace
`std` or `__gnu_cxx`, so libc++'s `std::__1`, libstdc++'s `std` and `std::__cxx11`), a `cir.libc.memcpy`,
`memmove` or `memset` operation becomes `memcpy.std`, `memmove.std` or `memset.std`, and a call of the module's
`memcpy`, `memmove`, `memset` or `memcmp` calls `memcpy.std`, ..., a declaration added after the module's
functions (only when some call needs it). Their models (`Model.memcpyStd`, `memmoveStd`, `memsetStd`,
`memcmpStd`) return at once for a length of 0, whatever the pointers, and otherwise are the plain models. The
program's own calls are unchanged, also in its own lambdas and functions that `std::` algorithms call.

The Gen of a C++ module changes in the function files of `std::` functions with such calls, and gains the added
declarations; C modules are unchanged.

### Library code by the definition's location (rog's audit, finding X1)

The namespace alone also took the program's code in namespace `std` for the library's: a program may specialize a
standard class template for its own types ([namespace.std]p2: `template<> struct std::hash<K>`, `std::less<K>`), and
the bodies of those specializations are the program's, so their `memcpy(buf, NULL, 0)` or `memcmp(NULL, NULL, 0)`
skipped the check (a missed UB; also in a function a program adds to `std`, undefined anyway by [namespace.std]p1).
`Frontend.isStdLibFunc` now also asks that the function be defined in the library's headers: the parser keeps the
file of each definition's location (`FuncDecl.srcFile`: the location after the body's closing brace, through location
aliases and the first part of a fused location, else the first parameter's; `cir2lean` does not write it), and
`Frontend.isStdLibPath` takes libc++'s `…/c++/v1/…` and libstdc++'s `…/c++/<version>/…`. Tests:
`tests/difftest/stdloc.cpp` (rog's n3c3.cpp, `CASES=stdloc_cases.txt`); stdmem_cases.txt unchanged.

## std::vector

`operator=(std::initializer_list<T>)` (`Model.vecAssignInitList`) gives a live vector the list's elements
(`Std.initListVals`, which the initializer-list constructor now shares) and returns `*this`. `assign(n, x)`
(`vecAssignFill`) gives it `n` copies of `x`; `x` a reference into the vector is undefined (C++ [sequence.reqmts],
`a.assign(n, t)`: "t is not a reference into a"). `assign(first, last)` (`vecAssignRange`) over `T*` / `const T*`
or contiguous iterators (`__wrap_iter`, `__normal_iterator`) gives it the elements of `[first, last)`, within one
array or container (`Std.rangePtrs`; empty between two null pointers), each loaded as `T`; an iterator into the
vector itself is undefined ("Neither i nor j are iterators into a"). libc++'s `assign(std::initializer_list<T>)`
runs its body, which calls the range `assign` with the list's begin and end. libc++'s instantiations of the range
`assign`, whose `enable_if` c++filt cannot demangle, are recognized structurally (a `std::vector<T>` member
`assign`, two parameters of one iterator type over `T`, `void`). libc++'s own code for these read the model's value
as its fields ("invalid memory read", 5 census mains in `assign(n, x)`, 2 in `operator=` of a list).

## std::string

`swap` (`strSwap`). `basic_string(first, last[, alloc])` (`strCtorRange rev`): `char` pointers, contiguous iterators
over `char` (a string's, a `std::vector<char>`'s) or (`rev`) their `std::reverse_iterator`s, whose range
`[last.current, first.current)` is read backwards (libc++'s `reverse_iterator` keeps the unused `__t_` before
`current`: the position is its last member); libc++'s instantiations, whose `enable_if` c++filt cannot demangle,
are recognized structurally, on a record that clang may name `std::string`. libstdc++'s range constructor, which
c++filt demangles, keeps running its code (the T3 units define it). libc++'s `basic_string(n, c[, alloc])`
(`strCtorFill`, decided on the CIR signature in `std::__1` only, as c++filt prints it as
`…basic_string<0>(char, allocator const&)`) makes `n` copies of `c`; its body called `__init(n, c)`, which
libc++'s library has (315 of the 357 corpus files instantiate it); libstdc++'s (34 T3 units define it) keeps running
its code.

libc++'s `operator+` of lvalues (string + string, + C string, + character, and C string or character + string)
calls `__concatenate_strings(alloc, string_view, string_view)` (`strConcat`): the result holds the two views'
characters and is returned by value under a fresh generation (`Std.retVec`). A character operand's view is a lone
object, so one character is read without a stride (`Std.readChars`). libc++ exports `operator+(const char*,
const string&)` from its library, without a body in the module (`strConcatCStr`, recognized in `std::__1` only:
libstdc++'s has its own code). The overloads on rvalues still run libc++'s code (`append`, `push_back`, the move
constructor; those that `insert` have no model).

libc++'s library has `compare(const char*) const` and `compare(pos, n1, const char*, n2) const` (`operator==` with
a C string calls the latter); no body in the module (`strCompareCStr`, `strCompareSub`): `char_traits<char>::compare`
over the first `min` of the lengths, as `unsigned char`s, then the lengths (`Std.compareChars`), -1, 0 or 1 as the
`memcmp` model (the value is unspecified beyond its sign); `pos1 > size()` throws `std::out_of_range`; only the
characters compared are read, and `[s, s + n2)` must be a valid range. `operator<` and `compare` of two strings run
libc++'s code, `char_traits<char>::compare` as `memcmp` over the strings' characters (vecmem's typed ranges): no
change, now with tests.

Each character these models copy or compare is read as a `char`: an indeterminate one is undefined
(C++ [basic.indet]; `char_traits::assign` and `copy` read each character).

## Narrowings

None: no case of the existing case files changes.

## Test labels changed

None in the existing case files. New: `tests/difftest/stdmem.cpp` (`CASES=stdmem_cases.txt`) and
`tests/difftest/contb3.cpp` (`CASES=contb3_cases.txt`), every case labelled.

## Gaps

Labelled UB in contb3_cases.txt, defined in C++: a string's `c_str()` as the C string of `compare(const char*)`
and of `operator+(const char*, const string&)` (`g_compare_c_str`, `g_plus_c_str`: `Std.readCStr` reads `char`
arrays, not a string's characters; the same holds for the older C string models). Not labelled: libstdc++'s
`operator+`, range constructor, `basic_string(n, c)` and `compare` of two strings (its own code, no model), the
`operator+` overloads that `insert`, and `compare(pos, n1, const char*)`.
