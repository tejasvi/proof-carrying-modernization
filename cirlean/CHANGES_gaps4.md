# gaps4: `std::string::reserve`; `fread` from standard input

Two programs of the static census blocked by one library function each.

- `std::string::reserve(n)` (libc++'s library; Shootout-C++ strcat) is the vector's model,
  `Model.vecReserve`: the characters stay, and since the capacity is not modelled every pointer and
  iterator into the string is invalidated (a fresh generation), as a reallocation would invalidate
  them; C++ keeps them valid when no reallocation happens, so this is the conservative choice the
  containers already make. As for the vector, `n` is not checked against `max_size()`: where libc++
  throws `length_error`, the model returns normally (a known deviation of both models).
- `fread(ptr, size, n, stream)` (Shootout-C++ wordfreq): standard input is at its end, as for `getchar`
  and `scanf`, so from `stdin` nothing is read and the result is 0 (C11 7.21.8.1p3; the end-of-file
  indicator is not modelled); `ptr` must still be valid (7.1.4p1). Any other stream is not modelled.
- `LibOp`: `fread` and gaps3's `__hash_memory` and `__next_prime` are the operations of one model,
  `Model.lib op`, run by `Std.libModel` (with its well-formedness lemma) behind one alternative of
  `Std.runModel`: `fread`'s own alternative, even with its arguments unmatched, made the automatic
  `WF_runModel` proof run out of heartbeats again. Further small models can join `LibOp`.

Pin census: 1183 of the 1812 programs without a static blocker, against 1181 at gaps3 (Shootout-C++ strcat
and wordfreq; none lost); the 193 dynamic mains as at gaps3 (172 run to their end, 17 UB, 4 timeouts).

## Narrowings

None.

## Test labels changed

None. New: `tests/difftest/gaps4.cpp` (`CASES=gaps4_cases.txt`, every case labelled: 6 MATCH, 2 UB: a pointer
into a string used after `reserve`, and `fread` into a null pointer).
