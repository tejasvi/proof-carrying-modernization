# arrnew: array new of classes with constructors

- `new T[n]` of a class with a constructor and a constant n was "array-to-pointer decay of a non-array"
  (vecfix's labelled gap, also without a vptr). CIR spells it as `operator new[]`, a `bitcast` of the
  storage to `T*`, a `bitcast` of that to `T(*)[n]`, an `array_to_ptrdecay` and a loop of constructor
  calls. The first typed view of the storage gives it the type `T[n]` and the pointer element 0, and the
  decay of that pointer, which designates an element and not an array, failed. A pointer to element 0 of an
  array of records converted to a pointer to the array's type now designates the array (`Ctx.convertPtr`,
  which holds the record conversion of `Ctx.convertPath` too, out of `evalSimple`: inline, the automatic
  `WF_evalSimple` proof ran out of heartbeats; in the `cir_exec` simp set), and a pointer to a lone record
  converted to `T(*)[1]` decays to that object, the element of an array of one (C11 6.5.6p7; `castVal`:
  `new T[1]`, whose storage the first typed view gives the type `T`). Arrays of scalars keep their element
  pointer: vectors are such arrays, and a vector access over a `float[4]` stays the access element by
  element (CHANGES_vecstore.md), for which an indeterminate element is undefined, where a load of the whole
  array would copy it (an earlier version of this change, for every array, made vecstore's
  `u_load_uninit` read 1). A size known only at run time already worked (CIR constructs the elements
  through the `T*` itself).
- Not modelled: the array cookie of a class with a non-trivial destructor (the element count stored before
  the elements, so the first typed view sees a `size_t` and the elements are bytes of it: "type-punned
  access").

## Narrowings

None.

## Test labels changed

`vecfix_cases.txt`: `g_value_init_array_new` (UB, the gap) is `v_value_init_array_new`, expected MATCH. New:
`tests/difftest/arrnew.cpp` (`CASES=arrnew_cases.txt`, every case labelled).
