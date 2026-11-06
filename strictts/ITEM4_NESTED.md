# Item 4: nested loops and calls in loop and callback bodies (branch `partial`, 2026-10-24)

## What changed (`StrictTS/Proof/Summarize.lean`, `StrictTS/Proof/CallbacksAt.lean`)

| form | how | examples |
|---|---|---|
| a loop or array callback inside a loop body or a callback | `ts_merge` (`mergeGoal`) summarizes the first loop or callback it meets with `ts_summarize`/`ts_callbacks` on the symbolic state of the enclosing iteration, then goes on; the outer step function contains the inner fold. The nested call keeps the enclosing call's heap facts (`Summarize.withNested`) and must leave no side goal | `sumProducts`, `countLess`, `uniqVals` |
| the outer counter read by an inner loop | a mutable variable that a loop never assigns (`Summarize.assignedSlots`) keeps its value instead of joining the fold's state | `countLess` |
| a callback that calls a program function | `ts_callbacks` unfolds the non-recursive callees (`Summarize.calleeLemmas`, as `ts_summarize` already did for loop bodies); a callee with a loop is summarized nested | `anyBig`, `sumSums` |
| a callback that reads the heap | pure in the world where the method calls it (the call's world; for `filter` the world after the result array is allocated): `arrFilter_pureAt`, `arrSome_pureAt`, `arrEvery_pureAt`, `arrFind_pureAt`, `arrFindIndex_pureAt`, used when the callback is not pure in every world | `diffWith`; public `cb_differenceWith`, `difference` |
| an in-place update of the array whose length the loop reads | the cell's content is a state of fixed size (`evalLoop_count_sized`, `{c // c.size = m0}`), its new content comes with a size obligation | `doubleInPlace` |

Smaller fixes found on the way: `ts_callbacks` runs the callback without error recovery (a
failing tactic inside `match` alternatives was admitted with an error instead of failing), takes
the facts that tell cells apart (`heapNeFacts`), and builds its lemma lists before its saved
state (their terms must survive a restore); a path that does not reduce now leaves the merge
goal stuck instead of failing, so a summary retries with the cell the path writes; tests on
the size of an updated array (`(xs.set j v).size`) are decided; a cell that an inner loop
rewrites from its start is detected as written.

## Measurement (frozen `git archive` copies, `scratch/meas/final_v1.sh`, `compare_v1.py`)

Before = master `c7de2cc`, after = `1b2451a` (= `c7de2cc` + item 4). The same inputs as for item 3
(`scratch/meas/pubsrc_1124`, `npsrc_1124`). Another project: asyncrace's kit
(`asyncrace/scratch/kit_loops`, the `ret` statements of the loops metric, 272 attempts, 1.2M
heartbeats and 120 s each), outputs untracked under `scratch/meas/cm_*`.

| | before `c7de2cc` | after `1b2451a` |
|---|---|---|
| bench equivalences proved | 40/44 | 40/44 |
| bench differences refuted | 23/23 | 23/23 |
| wrong verdicts | 0 | 0 |
| es-toolkit fixed pure callbacks | 36/47 | 40/47 (+`cb_differenceWith`, `cb_intersectionWith`, `cb_isSubsetWith`, `cb_uniqWith`) |
| es-toolkit generic@number | 2/39 | 4/39 (+`difference`, `intersection`) |
| es-toolkit `JS.Returns`, TheAlgorithms (dyn, generic) | 4/16, 1/44, 0/2 | the same |
| NoPanic attempts (es 7, cb 3, TA 11) | 3, 3, 9 | 3, 3, 9 |
| uniform NoPanic (302 files run) | 184 | 191 (+the four `cb_…With`, `difference`, `intersection`, `isSubset`) |
| another project loops metric (`ret`) | 14/272 | 14/272 (no attempt changes verdict) |

Nothing proved before is lost. On another project the first stuck constructs move a little (array
callback 52 → 51, external call 34 → 33, `for … of` 21 → 20, a branch on symbolic data 5 → 3)
while timeouts (10 → 14) and heartbeat limits (5 → 8) grow: the nested summaries get further and
then run out of budget. The timeouts are a net figure (10 attempts newly time out, 6 no longer
do) and mostly load: the kit's cap is 120 s of wall clock, and in a second after-run with the
machine less loaded (`893c0bd`, 9 timeouts) 7 of the 10 went back to their master
classification. Three time out in both after-runs and never on master (a module variable, a
counted loop and a callee not unfolded on master): the real cost of the nested attempts. The
attempt names went to autosplit, which profiles budget failures; they stay out of tracked files. asyncrace's reading of the 64 array-callback blockers: the `map`/`filter`
callbacks (24/18) make calls, extern calls, nest array operations or read record fields.

A first slowdown (heap facts computed by `ts_callbacks` before it checked for a callback at all,
every generic@number attempt 2-10 times slower) was found in a measurement run and fixed in
`9c95491`/`1b2451a` before the numbers above.

Follow-up `893c0bd`: `map` callbacks that read the heap (`arrMap_pureAt`, with heap facts for
the world of the call; example `addLen`). Measured the same way on frozen copies of master
`1c8ef91` (which has the state above merged) and the branch merged with it (`6a4de0a`): bench
43/44 → 43/44 (23/23, 0 wrong), every public set unchanged (cb 40/47, generic@number 4/39, …),
uniform NoPanic 191 → 191, another project `ret` 14 → 14 (no verdict changes; array callback 52 → 51,
symbolic side goals 10 → 12, heartbeat limits 12 → 9, timeouts 5 → 7). Nothing gained beyond the
example and nothing lost: the other project `map` callbacks stop at extern calls, module variables
and symbolic side goals before the heap read matters.

## Open items (for the handoff)

* selection sort: the inner loop's state holds the index of the minimum, read as `items[min]`;
  without an invariant (`i <= min < n`) the read does not evaluate on a symbolic state. A way in,
  like the fixed-size cells: a state component of type `{m : Nat // m < n}` (or `Fin n`) for a
  variable that is only ever assigned counter values, with the bound as the obligation.
* bubble sort: summarized (both loops, fixed-size cells), but `ts_auto`'s final `simp` over the
  nested fold runs past 400000 heartbeats. The fold carries the size proofs (`⟨H i s c, hH i s c⟩`)
  as big terms; after the rewrite they could be replaced by a hypothesis (assert the instantiated
  proof, replace it in the target by `replaceTargetDefEq`), or the final content generalized for
  `Returns`/`NoPanic` goals, where its value does not matter.
* `unionWith`/`xorWith`: `uniqWith(arr1.concat(arr2))` indexes an array of `c0.size + c1.size`
  elements, which the statement does not bound below `2^32`.
* `reduce` without an initial value (`Builtin.arrReduce1`, three TheAlgorithms NoPanic attempts:
  `binaryLCM`, `greatestCommonFactor`, `lowestCommonMultiple`) has no summary yet. The semantics
  (Core/Sem.lean) folds `(List.range n).tail` from `c0[0]` when `0 < n`, else throws a TypeError:
  a lemma `arrReduce1_pure'` with the result `if h : 0 < xs.size then some (.ok
  (xs.toList.tail.foldl g xs[0]), w) else exec (throwJS …) w` (helper: the fold over
  `(List.range l.length).tail` with the `dite` guard is `l.tail.foldl`, like `foldl_range_dite`)
  and a `ts_callbacks` branch with the callback's `(acc, x, i, arr)` arguments.
