# Item 3: loop forms for `JS.Returns` and equivalences (branch `partial`, 2026-10-24)

## What `ts_summarize` covers now (all in `StrictTS/Proof/Summarize.lean`)

| loop form | theorems | examples |
|---|---|---|
| `break`/`return` in `for … of` over strings, Maps, Sets | `evalForOfStr/Map/Set_summary_cells_brk/_ret` | `examples/Summarize/TsAutoLiveExits.lean` (6) |
| `break` in a counted loop (stop position kept) | `evalLoop_count_brk_aux`, `_pure_brk`, `_cells_brk` | public `cb_takeWhile` |
| bounds `i < a - c`, `i <= e`, `i <= a - c` (rewritten to `i < n'`) | `lt_ofNat_sub_ofNat_eq`, `le_ofNat_eq_lt_succ`, `le_ofNat_sub_ofNat_eq`, `le_ofNat_sub_one_eq` | `TsAutoBounds.lean`: `sumUpTo`, `isSorted`, `sumLe` |
| a start above the bound (counter ends at `max k0 n`) | `evalLoop_count_aux` (generalized) | `sumLeLast` |
| backwards `for (let i = xs.length - 1 | k0; i >= c | i > c; i--)`, with `break`/`return` | `evalLoop_down_cells`, `_ret`, `_brk` | `sumDown`, `sumDown10`, `lastNeg` |
| `return` whose iteration allocates (`return xs.slice(…)`) | `evalLoop_down_cells_retw` (exit world in the fold) | `dropRightPos`; public `cb_dropRightWhile`, `cb_takeRightWhile` |
| `while (i < n) { …; i++ }`, `while (i >= c) { …; i-- }` (step last, no exits) | `evalLoop_while_up_cells`, `evalLoop_down_while_cells` | `countWhile`, `sumWhile`, `sumWhileDown`, `countDown5` |
| `i < s.length` over a string, reading `s[i]`/`s.charAt(i)`; callees of the body unfolded | `JSStr.at?_natCast_of_lt`, `Summarize.calleeLemmas` | bench 13 (statement with string lengths) |
| backwards loop from the computed start `Math.min(Math.floor(n), m)`, test `i > c` | `evalLoop_split_start`, `F64.floor_min_eq_ofNat_min` (LibLemmas, own block) | `countDownMin`; bench 03 |

`ts_auto` (Auto.lean `isSummarizableLoop`) now also offers `while` loops to `ts_summarize`, so a
counted `while` behind a heap read (its start `xs.length - 1`) is summarized once the read is
evaluated (agreed with autosplit).

Tactic fixes found on the way: index facts enter the body's symbolic run as proof terms (a local
hypothesis cannot appear in the read-off step function); `by omega` checks run through
`proveProp?` (a failing `by omega` inside a term is logged as an error, not thrown); raw nat
literals (from unifying with `OfNat.ofNat`) are atoms for `omega` and are rewritten to numerals;
`mergeGoal` strips goal metadata; `splitRet` splits on the fold's flag (it carries the position
and the exit world).

## Final measurement (frozen `git archive` copies, `scratch/meas/final_v1.sh`)

Before = master `9b2f746` (it contains `d45ce9a`), after = `1d19bae` (= `9b2f746` + item 3).
Both use the same inputs, copied once: the emitted modules and attempt files of autosplit's
last run (`auto_fbfull`, in `scratch/meas/pubsrc_1124`) and public's uniform NoPanic files
(`scratch/nopanic`, in `scratch/meas/npsrc_1124`). The bench runs in three subsets
(`stream_v2.sh`), the NoPanic sweep with public's `np_plan.py`, `prove.sh` and `np_verdicts.py`
(`np_stream_v2.sh`, one file at a time). `scratch/meas/compare_v1.py` gives the table.

| | before `9b2f746` | after `1d19bae` |
|---|---|---|
| bench equivalences proved | 37/44 | 39/44 (+03 `countDown`, +13 `vowelCount`) |
| bench differences refuted | 23/23 | 23/23 |
| wrong verdicts | 0 | 0 |
| es-toolkit `JS.Returns` | 4/16 | 4/16 |
| es-toolkit generic@number | 2/39 | 2/39 |
| es-toolkit fixed pure callbacks | 26/47 | 36/47 |
| TheAlgorithms `JS.Returns` | 0/44 | 1/44 (+`isSortedArray`) |
| TheAlgorithms generic@number | 0/2 | 0/2 |
| NoPanic attempts (es 7, cb 3, TA 11) | 3, 3, 9 | 3, 3, 9 |
| uniform NoPanic, all sets (302 files run) | 172 | 183 |
| … es-toolkit fixed callbacks dyn | 28/47 | 38/47 |
| … TheAlgorithms dyn | 31/77 | 32/77 (+`isSortedArray`) |
| … es-toolkit dyn / generic@number dyn / strict, TA generic@number | 83/137, 16/23, 3 + 9, 2/6 | the same |

The ten new callback functions are the same in the `JS.Returns` attempts and in the uniform
NoPanic sweep: `cb_dropRightWhile`, `cb_takeRightWhile`, `cb_takeWhile` (counted loops: backwards,
with `return xs.slice(…)`, and forward with `break`), `cb_every`, `cb_findKey`, `cb_findValue`,
`cb_some` (a `for … of` over a `Map` with an early exit) and `cb_every_2`, `cb_find_2`, `cb_some_2`
(the same over a `Set`). Of the NoPanic blockers named in the assignment, `cb_chunkBy` stays: its
continuing iterations allocate a new chunk. Nothing proved before is lost: no bench pair, no
attempt, no NoPanic function.

Cost: the extra summaries are tried before a loop is given up, so the after runs are slower.
The NoPanic sweep took 61 min before and 70 min after (the same 302 files, one at a time, the two
sweeps side by side). The five open bench pairs took 112 s before and 139 s after (one after the
other).

Merged check: master moved on (`80b8bd1`: difftool's pair 37 and LibLemmas simprocs
`heapGetInsertKindNe`, `foldlFinRangePush`); the branch merged it cleanly (`269c386`). The same
streams on frozen copies of `80b8bd1` and `269c386`: bench 38/44 → 40/44 (+03, +13), 23/23,
0 wrong; the public attempts gain the same ten callback functions and `isSortedArray`; nothing
lost; the uniform NoPanic sweep on `269c386` gives the same 183 as on `1d19bae`. Again on master
`be829d7` (Auto.lean, LoopExit, Module changes) vs the merge `a2a6be3`: bench 38/44 → 40/44,
the same public gains, nothing lost.

Earlier runs on master `48aa653` (mid `3de3630`, `e09a0ac`) gave the same differences step by
step (cb 25 → 33 → 35/47, TA 0 → 1/44, bench 31/44 throughout, nothing lost).

## Left, with the reason

* public: `linearSearch` (`===` on `any` values may panic in the model), `uniqWith`/`unionWith`/
  `xorWith` (a callback `result.every(…)` inside the loop body), `isPerfectNumber`
  (`i < Math.sqrt(n)`), `addBinary`/`isPalindrome`/`exponentialSearch`/`fibonacciSearch`/
  `sentinelSearch` (`while` loops that are not counted: two counters, division, doubling), nested
  loops (`bubbleSort`, `insertionSort`, `CountSmallerItems`, `pascalsTriangle`,
  `sieveOfEratosthenes`), bodies that call a recursive function (`buildMaxHeap`, `HeapSort`,
  `parseNestedBrackets`), `Math.random()` in the body (`shuffle`, `shuffleArray`), `cb_chunkBy`
  (continuing iterations allocate).
* string loops in the uniform NoPanic sweep (`deburr`): the summary needs the string length to be
  at most `2^53`, which the NoPanic statements do not assume (difftool's `_wfs` statements do).
* bench 32 (string reverse): besides the relation modulo garbage cells (equiv-lean), a backwards
  counted loop that reads `s.charAt(i)`; the backwards summaries do not add the string-position
  facts yet (the forward ones do).
* other computed starts: forward loops from a variable, and `i >= c` from
  `Math.min(Math.floor(n), m)` (`-0` passes that test, so one iteration runs at `-0`).
* bench 23 (loop side from `n` after `Number.isInteger(n)`) is proved by difftool's concrete
  evaluation on master, not by a summary.
