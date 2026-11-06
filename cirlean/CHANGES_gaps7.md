# gaps7: stores of empty values dropped in C++ modules

The census main graph_cycle_check copies a `std::map`, and libc++'s `__tree(const __tree&)` builds its node
allocator (an empty class, a `[[no_unique_address]]` member of the compressed pair that holds `__end_node_`) from
`select_on_container_copy_construction`'s value. CIR's records leave the empty member out, so CIR stores its value
through a cast of the address it shares with `__end_node_` (`cir.store %13, %10 : !allocator`); cirrun's typed
store wrote that indeterminate empty value over `__end_node_`, and the later `*__root_ptr() = root`, a store into
`__end_node_.__left_`, was "invalid memory write".

- An empty class object has no value bits (C++ [intro.object]p9) and may share its address with another member
  ([dcl.attr.nouniqueaddr]); its trivial copy copies no bytes. So in a C++ module the frontend drops every
  `cir.store` and `cir.copy` of a type with no value representation (`Frontend.dropEmptyStores`, `emptyValueTy`):
  a complete record, not a union, whose members are padding, empty members or records of the same kind, and an
  array of such a type. C has no empty structures (only as a GNU extension), so C modules keep those
  operations. A frontend change only: Eval, the models and the proofs are unchanged.
- libc++'s `map`, `set` and `list` copy constructors build their allocators the same way: their copies run now
  (gaps7.cpp). A load of such a type is left as it is (none of the cases needs more).
- The cJSON Gen is byte-identical (C modules). Of the claimed T2/T3 units (fv_paper's scan manifest,
  stridescan/manifest.tsv: T2 102 units, T3 54, T3sp 12), 146 have modules with such operations, so their Gen
  changes: T2 80 (of its 81 C++ units), T3 54, T3sp 12; 2356 operations in 118 C++ unit files, at most 80 in one
  (counted with a scan of the raw parse, `emptyValueTy` on each `cir.store` / `cir.copy` of a C++ module; a unit
  with them gives a different Gen, one without the same Gen, checked on one of each).

Pin census (`pin_census_v2.sh`): static 1188 of 1812 as at next3 c934cb5; of the 193 dynamic mains 174 run to
their end, 15 stop with UB, 4 time out, against 173, 16 and 4 at c934cb5: graph_cycle_check runs to its end
(returning 0, as natively), where it was "invalid memory write".

## Narrowings

None.

## Test labels changed

None. New: `tests/difftest/gaps7.cpp` (`CASES=gaps7_cases.txt`, every case labelled: 8 MATCH: a
`[[no_unique_address]]` empty member built after and before the pointer it overlaps and assigned, map copy and
copy assignment, set and list copies).
