# vecfix: vectors without a constructor call, std::vector<bool>, zeroed vptrs

- A `std::vector` object that holds libc++'s members of an empty vector where no constructor of the model
  ran was "not a live std::vector". `vector()` is `constexpr`, so a global or static vector is
  constant-initialized (`#cir.zero`, no dynamic initialization calls the constructor), also as a member or an
  array element of one, and CIR may spell a defaulted constructor as the member stores. `readVec` reads such
  an object as an empty vector when every member is a null pointer or zero (`isEmptyVecLayout`), which is
  libc++'s representation of one, and the object's type is a `std::vector` record (`isVecObject`); `ensureVec`
  stores the empty container before `data`, `begin` or `end` forms a pointer into it (generation 0 has no
  element pointer). Such a global's destructor, registered with `__cxa_atexit`, also failed at the exit of
  any program that has one. Census mains: data_structures_disjoint_set and range_queries_prefix_sum_array.
- `vector(first, last[, alloc])` (`Model.vecRangeCtor`): the elements of a range of `T*` / `const T*` or
  contiguous iterators over `T`, which must lie within one array or container (C++ [sequence.reqmts]: a valid
  range), each loaded as `T`. libc++'s has an enable_if that c++filt cannot demangle; it is recognized
  structurally (a constructor of `std::vector<T>` with two parameters of one iterator type over `T`, and an
  optional allocator). sorting_selection_sort_iterative stopped at "object is not a live std::vector" after
  this constructor had run libc++'s code.
- libc++'s `std::vector<bool>` is modelled, rather than letting its code run: that code reads and writes
  whole words of bits, and its copying and growth paths read words they have not written yet, which the
  semantics rightly reports as indeterminate reads (census mains: "read of an indeterminate or ill-typed
  value"). The vector is `Val.vec g bs` of `bool`s, with `std::vector<T>`'s models for the constructors
  (default, allocator, copy, move, initializer list, size, fill, an iterator range of `bool` pointers), the
  destructor, assignment, `assign(n, x)`, `size`, `empty`, `push_back`, `pop_back`, `clear`, `reserve` and
  `swap`. `Model.vecBool` (`VecBoolOp`, `Std.vecBoolModel`) holds the members whose models differ:
  `operator[]` (also `const`) and `at` (`std::out_of_range` outside the vector) return libc++'s reference
  proxy, here the record `{element pointer, 1}`; the proxy's `operator bool`, `operator=(bool)` (returns the
  proxy), `operator=(const __bit_reference&)` and `flip` (`__bit_reference`, `__bit_const_reference`) read
  and write that element; `resize(n, x)` takes `x` by copy; `operator==` compares the sizes and the elements
  (libc++'s walks the iterators). A proxy formed before the vector reallocated (a new generation) no longer
  designates an element, as a reference into it. Not modelled: the iterators (`__bit_iterator`), `front`,
  `back`, the vector's `flip`, `assign(first, last)`, `emplace_back`; libc++'s code for them stops at the
  model's value ("invalid memory read"). libstdc++'s `std::vector<bool>` keeps running its code. Census mains:
  dynamic_programming_partition_problem, graph_bridge_finding_with_tarjan_algorithm, graph_hamiltons_cycle,
  math_sieve_of_eratosthenes.
- A zeroed vptr is a null pointer (`Ctx.zeroVal` of `vptr`; it had no zero value): value-initialization of a
  polymorphic object (`new T()`, `T{}` for a class without a user-provided default constructor) zeroes the
  object, its vptr too, before the constructor stores the vptr, and the `memset` that CIR emits for it failed
  ("memset: no zero value for the type"). A virtual call or a vtable read through a null vptr is undefined.
  The same zero value now serves the other zero-initializations: a global's `#cir.zero` initializer (static
  storage, zeroed before a dynamic initializer runs its constructor; the whole object was indeterminate, so
  a member the constructor leaves alone read as indeterminate instead of 0), `#cir.zero` constants, and
  zeroed heap storage typed as a polymorphic class. A global with a vptr that the module only declares
  (`std::cout`, which libc++'s library constructs) stays indeterminate, as before (`Ctx.holdsVptr`;
  `Module.initMem`). Census main: test_virtual_dispatch.

## Narrowings

- `vector(first, last)` with `last` before `first`, or the ends in different arrays, is UB (libc++'s code
  threw `std::length_error` for a reversed range).
- `std::vector<bool>`'s `operator[]` outside the vector is UB (libc++'s code read a bit of the word).

## Test labels changed

None in the existing case files. New: `tests/difftest/vecfix.cpp` and `vecfixg.cpp` (the constant-initialized
globals, whose destructors run at every case's exit; `CASES=vecfix_cases.txt`, every case labelled).
