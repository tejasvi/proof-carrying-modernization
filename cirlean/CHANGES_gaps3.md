# gaps3: libc++'s `__hash_memory` and `__next_prime`

The next static census gap by the programs it blocks: libc++'s hashing support in its library, which
the unordered containers call (2 programs, Shootout-C++ hash and hash2).

- `std::__1::__hash_memory(p, n)` (what libc++'s `std::hash` of string views and strings and
  `__gnu_cxx::hash<const char *>` call) and `std::__1::__next_prime(n)` (the bucket counts) are library
  models (`Model.libcxxHash`, `Std.libcxxHashModel`, `CIR/Std/Hash.lean`). `__hash_memory` is libc++'s
  `__murmur2_or_cityhash<size_t>` for a 64-bit `size_t`, CityHash64 in libc++'s ABI version 1 (for 4 to 8
  bytes, the first word shifted left by 3 in 32 bits, as without `_LIBCPP_ABI_FIX_CITYHASH_IMPLEMENTATION`),
  of the bytes of the representation of the object `p` points into (`Std.readBytes?`, through `objBytes`):
  undefined past its end, for an indeterminate byte and for a pointer's byte. The characters of a
  `std::string`, a container in the semantics, are not read (not modelled; `g_hash_string` below).
  `__next_prime(n)` is 0 for 0 and otherwise the smallest prime not below `n`, as libc++'s `src/hash.cpp`
  computes it (its table of small primes, then the candidates of the 210-wheel, by trial division); its
  `overflow_error` above `2^64 - 59` is not modelled. Checked against libc++'s library (`libc++.a` of the
  CIR side's libc++, natively): `__hash_memory` of 0 to 200 bytes and `__next_prime` of 17 values, and
  `gaps3.cpp`'s cases (`v_hash_values` included) give the same results.
- `longjmp`'s model moved out of `runModel` into `Std.longjmpModel`, unchanged: with the new model's
  alternative, the automatic `WF_runModel` proof ran out of heartbeats splitting `runModel`'s `match`;
  `longjmp` and `libcxxHash` now take one alternative each, with their arguments matched in the helper
  (each with its well-formedness lemma).

Pin census: 1181 of the 1812 programs without a static blocker, against 1179 at gaps2 (the two programs
above; none lost); the 193 dynamic mains as at gaps2 (172 run to their end, 17 UB, 4 timeouts).

## Narrowings

None.

## Test labels changed

None. New: `tests/difftest/gaps3.cpp` (`CASES=gaps3_cases.txt`, every case labelled: 5 MATCH; 2 MISMATCH,
`v_hash_values`, libc++'s hashes against libstdc++'s natively; 2 UB: indeterminate bytes hashed, and the gap
`g_hash_string`).
