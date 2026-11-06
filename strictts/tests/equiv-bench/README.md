# Equivalence benchmark

67 refactoring pairs `NN_name/{old.ts,new.ts,expected}`: 44 equivalent refactorings (loops vs
`reduce`/`map`/`filter`/`some`/`every`/`find`/`findIndex`/`includes`, `for` vs `for…of`, `while`
vs `for`, extract/inline variable and function, De Morgan, ternaries, early returns, guard
clauses, `switch` vs if-chains, string building, int32 idioms, recursion vs loop, loop fusion,
reordering, renaming, optional chaining, `??`, Map counting, class methods, async, bigint,
tuples, …) and 23 subtly different ones (NaN in `indexOf`/`includes`, `-0` in `Math.abs`,
`Math.round`, `Set` and clamps, `||` vs `??`, default `sort`, off-by-one, rounding beyond 2^53,
code units vs code points, `Map` vs object key order, mutating vs copying an argument, error
types, async interleaving, `Object.is`, `floor` vs `trunc`, `parseInt` vs `Number`, `trim`,
`substring` vs `slice`, `%` vs `&`). `expected` starts with `equivalent` or `different`, followed
by a description. Pair 22 was written as an equivalence; the fuzzer found that `-0` passes its
guard, so it is labelled `different` and pair 67 is the corrected equivalence.

```sh
tools/run.sh 0.6 590 node tools/difftool/dist/cli.js bench tests/equiv-bench [--json out.json]
```

Results (10-24, measured on git-archive copies, three bench processes in parallel): before =
master eb67836 (the lead's measurement), after = branch difftool 774ed50 (master d2d0d78, the
same tree measured as f5543cf with 42/44, plus pair 32).

| | before | after |
|---|---|---|
| equivalences PROVED | 40/44: 32 for every world, 5 for allocated arguments, 2 (13, 35) also assume string lengths < 2^53, 1 (37) also allocated object arguments | 43/44: the same 40, and 3 (32, 36, 44) under the weaker observational statement |
| differences REFUTED | 23/23 (21 confirmed by Lean) | 23/23 (21 confirmed by Lean) |
| wrong verdicts | 0 | 0 |

Every other pair has the same verdict, Lean confirmation and statement before and after. The
observational statement (`equiv_<id>_obs`, attempted only after every equality statement failed)
is WEAKER than equality of worlds: the cells the callee allocated (other than a returned array)
and the allocation counter are not compared (tools/difftool/INTERFACE.md, Verdicts). 32 is proved
by `ObsEq w.next`: `split("")` allocates an array the caller never sees; the backwards `charAt`
loop is summarized (`dtToIntOfNat` bounds the position by 2^53), and the fold lemmas of
StrictTS/Proof/LibLemmas.lean ("Reversing a string") equate `join("")` of the reversed parts with
the loop's fold (`foldrFstUnit`, `foldr_val_str`, `foldl_append_eq_foldr`). 36 is proved
by `ArrObs w.next`: `xs.concat([])` allocates `[]` first, so the sorted copy is at `w.next + 1`
against `w.next`, with the same contents (the same `sortBy` run on the elements of `xs`;
`dtFreshRead` reads `xs` through the allocation of `[]`). 44 is proved by `ObsEq w.next`: the new
version's `Map` is a fresh cell the caller never sees, and `get` on the literal map runs by the
explicit-entry lemmas `JSMap.get?_mk_*`/`JSMap.set_mk_*` (StrictTS/Proof/LibLemmas.lean).

Earlier (master d45ce9a: 31/44, 27 for every world and 4 for allocated arguments), newly proved
on the difftool branch: 10 (flag loop ≡ `includes`, string elements), 18 (`switch` ≡ if-chain on a
string-literal union), 23 (recursive factorial ≡ loop, behind `Number.isInteger(n)` and
`0 <= n <= 20`), 24 (loop fusion) for every world; 19 (counted join loop ≡ `join(",")`) for
allocated arguments; 35 (`slice(0, p.length) === p` ≡ `startsWith(p)`) for allocated arguments
with string lengths below 2^53; 37 (a class method: `push` then a counted loop over the field ≡
`push` then `for … of`) for allocated arguments and objects; 03 and 13 came with partial's
counted-loop forms (Summarize.lean). No pair proved before is lost, and no statement became weaker.
`REFUTED*` = counterexample confirmed in Node only because the function is outside the StrictTS
subset. "allocated-arguments" means the theorem holds for every world in which the argument
arrays, maps and sets are allocated cells (`hw`, `hn`, `hs`), which every state of a run
satisfies; "allocated-arguments-strlen" also assumes that every string argument has at most
2^53 - 1 code units (`hl`, the maximum length of an ECMAScript String, ECMA-262 6.1.4);
"allocated-arguments-objects" also assumes that every object argument is an allocated cell with
initialised fields and its array fields allocated cells with fewer than 2^32 - 1 elements (`ho`;
room for one `push`). Pair 19
needs the array bound (the loop index is a double), pair 35 the string bound (in the model a longer
`p.length` rounds and the slice can be shorter than `p`).

What made the new proofs (StrictTS/Proof/LibLemmas.lean, "Bench lemmas (difftool block)";
StrictTS/Proof/Literals.lean; the difftool default script):

* 18: `ts_enum_cases` splits the enum argument into its members; the simprocs
  `reduceListGetLit`/`reduceListGetElemLit` (a member of the literal list) and
  `reduceOfStringBEq`/`reduceOfStringEq` (two string literals compared by the kernel) evaluate the
  narrowing that the translator lowers to `enumToStr` and string `===`.
* 10: `foldl_flag_true_eq` / `foldl_flag_true_dec` (and the `false` forms): the fold of a flag loop
  with an equality or other decidable test is `Array.any`; `Conv.svz_str` (SameValueZero of
  strings is `==`).
* 24: the simproc `foldlPairSplit` (`foldl_pair_split`): a fold over a pair of accumulators, each
  reading only its own, is a pair of folds; `foldl_keep`.
* 19: `foldl_val_str`, `toStr_match_ite`, `F64.ofNat_fin_gt_zero`, `foldl_finRange_sep`,
  `ofFn_toStr_getElem` (a `↓` lemma), the simproc `reduceOfFnZero`; the default script retries the
  goals `ts_auto` leaves after a case split with the case's equations substituted (`subst_vars`).
* 35: the allocated-arguments-strlen statement (string arguments within the maximum length);
  `Prim.intArg_ofNat_lt`, `Prim.posArg_ofNat_lt`.
* 37: the allocated-arguments-objects statement (`equiv_<id>_wfo`); the new version's `TT` and
  `«Cart».fields` emitted as aliases of the old ones (otherwise the two versions read the object
  under different heap keys and `Val New.TT` is another type to `simp`); the simprocs
  `heapGetInsertKindNe` (a read of the object past the write to the array) and
  `foldlFinRangePush` (the counted loop over `c.push x` is the fold over `c` and one step);
  `ts_auto [Array.size_push]` (the index bound of the summary) and a `simp_all` closer.
* 23: the first alternative of the default script (when a called function tests
  `Number.isInteger`): `dt_int_cases` splits `n` into `-0, 0, …, 20` (`F64.int_range_cases`);
  `dt_eval_calls` evaluates `fact(k)` with each call unfolded once over all cases (memoized);
  `dt_eval_loops` runs the loop of the new version on each value (tools/difftool/lean/DiffPrelude.lean).

The open equivalence and what it needs to prove its observational statement (`ArrObs`; no
equality statement can hold, as the two versions allocate different cells):

| pair | what is missing |
|---|---|
| 34_dedupe_strings | the old loop writes two cells (the `Set` and the result array) and `ts_summarize` supports one; then the invariant "seen = elements of out" relating the two folds (a lockstep rule) |

All pairs (after):

| pair | expected | verdict | evidence |
|---|---|---|---|
| 01_loop_to_reduce | equivalent | PROVED | theorem checked |
| 02_for_to_forof | equivalent | PROVED | theorem checked (allocated-arguments statement) |
| 03_while_to_for | equivalent | PROVED | theorem checked |
| 04_map_loop | equivalent | PROVED | theorem checked (allocated-arguments statement) |
| 05_filter_loop | equivalent | PROVED | theorem checked (allocated-arguments statement) |
| 06_some_loop | equivalent | PROVED | theorem checked |
| 07_every_loop | equivalent | PROVED | theorem checked |
| 08_find_loop | equivalent | PROVED | theorem checked |
| 09_findindex_loop | equivalent | PROVED | theorem checked (allocated-arguments statement) |
| 10_includes_strings | equivalent | PROVED | theorem checked |
| 11_extract_variable | equivalent | PROVED | theorem checked |
| 12_extract_function | equivalent | PROVED | theorem checked |
| 13_inline_function | equivalent | PROVED | theorem checked (allocated-arguments-strlen statement) |
| 14_de_morgan | equivalent | PROVED | theorem checked |
| 15_if_else_ternary | equivalent | PROVED | theorem checked |
| 16_early_return_nested | equivalent | PROVED | theorem checked |
| 17_guard_clauses | equivalent | PROVED | theorem checked |
| 18_switch_ifchain | equivalent | PROVED | theorem checked |
| 19_concat_join | equivalent | PROVED | theorem checked (allocated-arguments statement) |
| 20_template_concat | equivalent | PROVED | theorem checked |
| 21_int32_idiom | equivalent | PROVED | theorem checked |
| 22_floor_div_shift_negzero | different | REFUTED | `half(-0)`: old return -0; new return 0 (Lean-confirmed) |
| 23_recursion_to_loop | equivalent | PROVED | theorem checked |
| 24_loop_fusion | equivalent | PROVED | theorem checked |
| 25_reorder_independent | equivalent | PROVED | theorem checked |
| 26_rename_locals | equivalent | PROVED | theorem checked |
| 27_compound_assign | equivalent | PROVED | theorem checked |
| 28_boolean_simplify | equivalent | PROVED | theorem checked |
| 29_optional_chain | equivalent | PROVED | theorem checked |
| 30_nullish_default | equivalent | PROVED | theorem checked |
| 31_max_reduce | equivalent | PROVED | theorem checked |
| 32_string_reverse | equivalent | PROVED | theorem checked (observational statement) |
| 33_count_map | equivalent | PROVED | theorem checked |
| 34_dedupe_strings | equivalent | UNKNOWN | no proof: loops (needs loop summarization or a lockstep rule); allocation differs (equivalence modulo fresh allocation); allocated-arguments statement: loops (n |
| 35_startswith | equivalent | PROVED | theorem checked (allocated-arguments-strlen statement) |
| 36_array_copy | equivalent | PROVED | theorem checked (observational statement) |
| 37_class_method | equivalent | PROVED | theorem checked (allocated-arguments-objects statement) |
| 38_async_refactor | equivalent | PROVED | theorem checked |
| 39_bigint_refactor | equivalent | PROVED | theorem checked |
| 40_tuple_destructure | equivalent | PROVED | theorem checked |
| 41_optional_default | equivalent | PROVED | theorem checked |
| 42_string_indexof_includes | equivalent | PROVED | theorem checked |
| 43_min_commuted | equivalent | PROVED | theorem checked |
| 44_map_lookup | equivalent | PROVED | theorem checked (observational statement) |
| 45_indexof_includes_nan | different | REFUTED | `contains([NaN], NaN)`: old return false; new return true (Lean-confirmed) |
| 46_abs_negzero | different | REFUTED | `magnitude(-0)`: old return -0; new return 0 (Lean-confirmed) |
| 47_or_vs_nullish | different | REFUTED | `limitOf(0)`: old return 10; new return 0 (Lean-confirmed) |
| 48_default_sort | different | REFUTED | `ordered([-2, -450])`: old return [-2, -450]; new return [-450, -2] (Node only: outside the subset) |
| 49_off_by_one | different | REFUTED | `sumAll([8])`: old return 8; new return 0 (Lean-confirmed) |
| 50_overflow_2p53 | different | REFUTED | `nextPrev(0.1)`: old return 0.10000000000000009; new return 0.1 (Lean-confirmed) |
| 51_code_units_vs_points | different | REFUTED | `charCount("😀")`: old return 2; new return 1 (Lean-confirmed) |
| 52_map_vs_object_order | different | REFUTED | `firstSeen(["", "1"])`: old return ["", "1"]; new return ["1", ""] (Lean-confirmed) |
| 53_mutate_vs_copy | different | REFUTED | `median([7, 0])`: old return 7; args after ([0, 7]); new return 7; args after ([7, 0]) (Lean-confirmed) |
| 54_error_type | different | REFUTED | `parseAge("A")`: old throw Error: bad age: A; new throw TypeError: bad age: A (Lean-confirmed) |
| 55_async_ordering | different | REFUTED | `run("", "")`: old resolve "1,1,2,2"; new resolve "1,2,1,2" (Lean-confirmed) |
| 56_object_is | different | REFUTED | `sameValue(NaN, NaN)`: old return false; new return true (Node only: outside the subset) |
| 57_floor_trunc | different | REFUTED | `bucket(5, -7)`: old return -1; new return -0 (Lean-confirmed) |
| 58_parseint_number | different | REFUTED | `qty("1x")`: old return 1; new return 0 (Lean-confirmed) |
| 59_set_negzero | different | REFUTED | `distinct([-0])`: old return [0]; new return [-0] (Lean-confirmed) |
| 60_clamp_negzero | different | REFUTED | `clamp(6, 433, 1)`: old return 1; new return 433 (Lean-confirmed) |
| 61_trim_custom | different | REFUTED | `clean(" ")`: old return ""; new return " " (Lean-confirmed) |
| 62_substring_slice | different | REFUTED | `tail("😀", 1)`: old return "\ude00"; new return "😀" (Lean-confirmed) |
| 63_round_floor_half | different | REFUTED | `nearest(-0)`: old return -0; new return 0 (Lean-confirmed) |
| 64_mod_vs_and | different | REFUTED | `isOdd(-1)`: old return false; new return true (Lean-confirmed) |
| 65_reverse_mutating | different | REFUTED | `lastFirst(["", " "])`: old return "  "; args after ([" ", ""]); new return "  "; args after (["", " "]) (Lean-confirmed) |
| 66_min_ternary | different | REFUTED | `lower(NaN, 1)`: old return 1; new return NaN (Lean-confirmed) |
| 67_floor_div_shift_int32 | equivalent | PROVED | theorem checked |
