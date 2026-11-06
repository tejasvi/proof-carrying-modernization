# StrictTS on public TypeScript projects (2026-10-23)

Subset coverage, Lean emission and automatic proof rate of StrictTS on two public, strictly
typed TypeScript code bases, measured with the translator and tactics of master `5044b3c`
(Lean 4.35). The projects' sources are not part of this repository: `tools/public/fetch.sh`
downloads them at the pinned commits into `scratch/projects/` (gitignored); the per-function
tables in `tools/public/results/` hold names, line numbers and verdicts only.

| | es-toolkit v1.52.0 | TheAlgorithms/TypeScript 19b4ced |
|---|---|---|
| functions / non-blank LOC | 794 / 9,427 | 234 / 2,635 |
| strict subset: functions covered | 230 (29.0%) | 163 (69.7%) |
| strict subset: LOC covered | 1,509 (16.0%) | 1,529 (58.0%) |
| with dyn: functions covered | 329 (41.4%) | 166 (70.9%) |
| with dyn: LOC covered | 2,296 (24.4%) | 1,561 (59.2%) |
| emitted Lean modules (strict / dyn / generic wrappers / pure-callback wrappers) | 1,322 / 1,846 / 2,493 / 1,802 lines, 0 errors | 1,924 / 1,949 / 176 / - lines, 0 errors |
| `ts_auto` attempts (`JS.Returns`, functions with a loop or an array callback) | 51 | 44 |
| PROVED | 5 (3 + 2 that return a closure) | 0 |
| statement false for some input (classes A, B, N, M) | 41 | 31 |
| **PROVED / attempts whose statement may be true** | **5/10** | **0/13** |
| callback functions with one fixed pure callback: PROVED / attempts (/ may be true) | 23/47 (23/44, 52%) | (none take a callback) |
| **uniform `JS.NoPanic`, every emitted function (master `e57150b`): PROVED / attempts, strict; dyn** | **144/191; 174/245** | **36/82; 36/83** |
| counterexamples confirmed in Node (dyn): latent bugs / unsound reads tolerated / model limitations | 1 / 2 / 11 | 6 / 9 / 0 |
| separate result: the attempts that reach `String.matchAll` and `RegExpExecArray.get:[]`, with the two ECMA-262 host specifications as hypotheses (master `9e56ea6`, the same on `883a989`): PROVED with / without | 19/22 / 2/22 | 1/1 / 0/1 |

## Uniform NoPanic on master `e57150b` (2026-10-27)

The sweep of the section on `2ea47b8` below, redone on a git-archive copy of master `e57150b`
with the same procedure and limits and one change in the attempt files: they import the
library's root `StrictTS` instead of `StrictTS.Proof.Auto`, so that `ts_auto` sees the lemma set
of a user of the library, as the difftool's generated files do. Before, four modules with
`@[ts_sym]` lemmas were out of reach because only the root imports them:
`StrictTS.Proof.DynNullish` (`43132a8`), `StrictTS.Proof.Eval`, `StrictTS.Proof.Bits` and the
new `StrictTS.Proof.DynOpt` (`9e54bdb`: an unknown value passed to a `value?: unknown`
parameter). The coverage reports and all emitted modules are byte-identical to those of
`2ea47b8` (the translation of uncalled module-level const arrows is off in coverage mode; the
wrapper modules differ only in the path in their header comment).

**Summary.** es-toolkit 144 of 191 functions proved (75%) in the strict subset and 174 of 245
(71%) with dyn, TheAlgorithms 36 of 82 (44%) and 36 of 83 (43%); on `2ea47b8` they were 144/191,
167/245, 36/82 and 36/83. The 7 new proofs are es-toolkit `unknown` predicates with dyn; no proof
is lost and no other verdict changes. The counterexamples are those of `2ea47b8` (the same 29 dyn
functions, inputs and classes), every UNKNOWN attempt stops at the same construct as on
`2ea47b8`, and the search finds no panic in any proved function.

| project | mode | attempts, 2ea47b8 | attempts, e57150b | PROVED, 2ea47b8 | PROVED, e57150b | COUNTEREXAMPLE, 2ea47b8 | COUNTEREXAMPLE, e57150b (latent bug / tolerated / limitation) | UNKNOWN, 2ea47b8 | UNKNOWN, e57150b |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit | strict | 191 | 191 | 144 (75%) | 144 (75%) | 1 (1/0/0) | 1 (1/0/0) | 46 | 46 |
| es-toolkit | dyn | 245 | 245 | 167 (68%) | 174 (71%) | 14 (1/2/11) | 14 (1/2/11) | 64 | 57 |
| TheAlgorithms | strict | 82 | 82 | 36 (44%) | 36 (44%) | 15 (6/9/0) | 15 (6/9/0) | 31 | 31 |
| TheAlgorithms | dyn | 83 | 83 | 36 (43%) | 36 (43%) | 15 (6/9/0) | 15 (6/9/0) | 32 | 32 |

Per function (es-toolkit, dyn only):

* Proved now (7 attempts, all were UNKNOWN): `isNil` (both versions, `src/predicate` and
  `src/compat/predicate`) and `nullishRank` (was: an undecided test on a value read at run time),
  `isNull` and `isUndefined` (both versions; was: a `Dyn.eq` result not decided).
* The lemmas they need: each of the 7 proofs mentions lemmas of `StrictTS.Proof.DynNullish` and of
  no other module outside `StrictTS.Proof.Auto`'s imports (`np_used`), and each is proved again
  with `import StrictTS.Proof.Auto` and `import StrictTS.Proof.DynNullish` alone. The change
  against `2ea47b8` comes from the lemma scope: the `DynNullish` lemmas of `43132a8` (`===` of an
  unknown value against `undefined` or `null` always answers) now reach the attempts. The
  `DynOpt` lemmas move no verdict and no first stuck construct in this sweep.
* Lost proofs: none. Counterexamples: unchanged.

Tables for `e57150b`:

| functions | mode | attempts | PROVED | COUNTEREXAMPLE: latent bug | unsound read tolerated | model limitation | Node inconclusive | UNKNOWN | not attempted (callback parameter) |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit fixed callbacks | dyn | 51 | 44 | 0 | 2 | 0 | 0 | 5 | 0 |
| es-toolkit fixed callbacks | strict | 45 | 42 | 0 | 0 | 0 | 0 | 3 | 0 |
| es-toolkit | dyn | 157 | 101 | 0 | 0 | 11 | 0 | 45 | 0 |
| es-toolkit generic@number | dyn | 37 | 29 | 1 | 0 | 0 | 0 | 7 | 59 |
| es-toolkit generic@number | strict | 36 | 29 | 1 | 0 | 0 | 0 | 6 | 49 |
| es-toolkit | strict | 110 | 73 | 0 | 0 | 0 | 0 | 37 | 0 |
| TheAlgorithms | dyn | 77 | 34 | 6 | 9 | 0 | 0 | 28 | 0 |
| TheAlgorithms generic@number | dyn | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms generic@number | strict | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms | strict | 76 | 34 | 6 | 9 | 0 | 0 | 27 | 0 |

UNKNOWN by first stuck construct: as in the `2ea47b8` table below, less the 7 new proofs (dyn:
dyn operation result not decided 5 → 1, `invariant`; undecided test on a value read at run
time 4 → 1, `eq`).

The search finds no panic in any PROVED function (cross-check: 233 searches; 222 finished with
300 inputs and 8 more with 100 small ones; 3 did not: `logTwo`, `squareRoot`,
`TreeNode<number>.new`). Of the 89 UNKNOWN dyn functions, 74 were searched without a panic, 6
have argument types the search does not generate, and for 9 no pass finished (the same as on
`2ea47b8`).

`np_used` (`tools/public/lean/NoPanicDiag.lean`), as first written, read only the theorem's type:
in Lean 4.35 `ConstantInfo.value?` returns the proof of a theorem only with `allowOpaque := true`.
So the `NPUSED` lines of the main run say `none`; the attribution above comes from rerunning the 7
attempts with the fix (`attr/`; the run with `DynNullish` alone in `attr_abl/`).

Cost: 1.31 core-h metered (the guard logs' core-seconds summed): build, emission and elaboration
0.09; 359 proof files 0.64; search 0.27; Node checks 0.03; cross-check 0.28; attribution 0.004.
Proof files took 5 to 128 s each (300 s cap, never reached).

## Uniform NoPanic on master `2ea47b8` (2026-10-27)

The sweep of the section "Uniform NoPanic" below, redone on a git-archive copy of master
`2ea47b8`: modules emitted again, every attempt run, and the counterexample search, the Node
checks and the cross-check redone, with the same statement, hypotheses, limits and verdicts
(`maxHeartbeats 1000000`, generic functions at `T := number`, higher-order functions through
their `cb_*` wrappers). Since `881c69c` the translator emits the covered generic functions at one
instance by default; the base modules are emitted with `--no-emit-generics`
(`EMIT_FLAGS` of `tools/public/coverage.sh`), so that generic functions stay in the `T := number`
sets as before (the coverage report is the same with and without the flag).

**Summary.** es-toolkit 144 of 191 functions proved (75%) in the strict subset and 167 of 245
(68%) with dyn, TheAlgorithms 36 of 82 (44%) and 36 of 83 (43%); on `562bde2` (with the six
`s[i]` functions from `9e56ea6`) they were 118/164, 138/209, 35/82 and 35/83. No proof is lost and
no new latent bug appears. The translator changes since `562bde2`, among them the nullish test
`x == null` (`43132a8`), widen the es-toolkit coverage (strict 236 → 277 of 794 functions, dyn
367 → 422; TheAlgorithms unchanged): 63 new attempts (27 strict, 36 dyn), 31 of them proved. 13 old
functions are proved now, strict and dyn alike; the 3 new counterexamples are 2 reads that the
code tolerates and 1 model limitation. The search finds no panic in any proved function.

| project | mode | attempts, 562bde2/9e56ea6 | attempts, 2ea47b8 | PROVED, 562bde2/9e56ea6 | PROVED, 2ea47b8 | COUNTEREXAMPLE, 562bde2/9e56ea6 | COUNTEREXAMPLE, 2ea47b8 (latent bug / tolerated / limitation) | UNKNOWN, 562bde2/9e56ea6 | UNKNOWN, 2ea47b8 |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit | strict | 164 | 191 | 118 (72%) | 144 (75%) | 1 (1/0/0) | 1 (1/0/0) | 45 | 46 |
| es-toolkit | dyn | 209 | 245 | 138 (66%) | 167 (68%) | 11 (1/0/10) | 14 (1/2/11) | 60 | 64 |
| TheAlgorithms | strict | 82 | 82 | 35 (43%) | 36 (44%) | 15 (6/9/0) | 15 (6/9/0) | 32 | 31 |
| TheAlgorithms | dyn | 83 | 83 | 35 (42%) | 36 (43%) | 15 (6/9/0) | 15 (6/9/0) | 33 | 32 |

Per function (strict and dyn alike unless marked; for UNKNOWN, the first stuck construct):

* Proved now (13 functions, 26 attempts; all were UNKNOWN): TheAlgorithms `bubbleSort` (was: a
  `while`/`for` loop); es-toolkit `bgHex`, `hex`, `parseHex` (was: the answer of `RegExp.test`;
  `bgHex` is one of the three regex attempts that the host specifications did not prove on
  `9e56ea6`), `escapeString`, `uniqueId` (was: a module variable cell), `difference<number>`,
  `intersection<number>`, `isSubset<number>`, `cb_differenceWith`, `cb_intersectionWith`,
  `cb_isSubsetWith` (was: a `filter` callback that captures variables), `cb_uniqWith` (was: a
  `while`/`for` loop).
* Lost proofs: none. The old attempts keep the counterexamples of `562bde2` (the same 26 dyn
  functions, inputs and classes).
* UNKNOWN at another construct: `deburr`, `escape` and `unescape` now reach the heartbeat limit
  (were: a `while`/`for` loop; `for … of` over an array); `parseNestedBrackets` ends within it
  again, at the counted loop over the string; `createPadding` and `stringSize` get past the module
  variable cell and stop at an undecided test on strings.
* New attempts, all es-toolkit (the functions of the wider coverage, generic ones at
  `T := number`). PROVED: `getUnicodeWordPattern`, `inRange` (number and bigint), `random`,
  `isBrowser` and `isNode` (dyn), `constant<number>`, `drop<number>`, `take<number>`,
  `toArray<number>`, `initial<number>`, `last<number>`, `tail<number>`, `head<number>` on an
  array, `count<number>` and `head<number>` in curried form, `cb_partition_4` (dyn).
  COUNTEREXAMPLE (dyn; table below): `cb_reduce`, `cb_reduce_2` (unsound read tolerated),
  `isArrayLike` (model limitation). UNKNOWN: `clamp` (number and bigint), `endsWith`,
  `startsWith`, `parseLength` (other side condition); `Mutex.release`, `handleStdin` (cell of a
  reference below the first level); `Semaphore.release` (call of a function value read from the
  heap); `isNil` (dyn, two attempts: undecided test on a value read at run time);
  `parseAbortSignal` (external call answer); `defaultTo<number, number>`, `isNotNil<number>`
  (expression: the selection on a union member); `count<number>` and `head<number>` on an
  `Iterator` record and `cb_partition_3` (dyn) (call of a function value: the record's `next`).
  These last three take an `Iterator` record (`e2c2d05`) whose `next` is a function: as with a
  callback parameter, the statement quantifies over every `next` and cannot be proved
  (`nopanic.py` does not yet route such records to fixed-callback wrappers).

| new counterexample (dyn) | API | input | Lean panic | Node, with checks | Node, checks off |
|---|---|---|---|---|---|
| `cb_reduce` (unsound read tolerated) | exported | `[new Map([[3.8183909599847904e+214, 5], [-380.5, 0], [-9....` | non-null assertion on undefined | violation: `src/map/reduce.ts:42:24 initialValue!` | returned `5` (declared `number`) |
| `cb_reduce_2` (unsound read tolerated) | exported | `[new Set([-499.5, 0]), undefined]` | non-null assertion on undefined | violation: `src/set/reduce.ts:35:24 initialValue!` | returned `-499.5` (declared `number`) |
| `isArrayLike` (model limitation) | exported | `[true]` | non-null assertion on undefined | returned: `false` | - |

`cb_reduce` and `cb_reduce_2` are es-toolkit's `reduce` over a Map and over a Set with a fixed
callback and no initial value: the code reads `initialValue!`, an `undefined` that the types
exclude, then tests the accumulator for `null` and takes the first entry instead, so the result
is a number. In `isArrayLike(true)` the model stops at the cast `value as ArrayLike<unknown>` of a
boolean (a cast to an external type), where JavaScript reads `true.length` as `undefined` and
returns `false`.

Tables for `2ea47b8`:

| functions | mode | attempts | PROVED | COUNTEREXAMPLE: latent bug | unsound read tolerated | model limitation | Node inconclusive | UNKNOWN | not attempted (callback parameter) |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit fixed callbacks | dyn | 51 | 44 | 0 | 2 | 0 | 0 | 5 | 0 |
| es-toolkit fixed callbacks | strict | 45 | 42 | 0 | 0 | 0 | 0 | 3 | 0 |
| es-toolkit | dyn | 157 | 94 | 0 | 0 | 11 | 0 | 52 | 0 |
| es-toolkit generic@number | dyn | 37 | 29 | 1 | 0 | 0 | 0 | 7 | 59 |
| es-toolkit generic@number | strict | 36 | 29 | 1 | 0 | 0 | 0 | 6 | 49 |
| es-toolkit | strict | 110 | 73 | 0 | 0 | 0 | 0 | 37 | 0 |
| TheAlgorithms | dyn | 77 | 34 | 6 | 9 | 0 | 0 | 28 | 0 |
| TheAlgorithms generic@number | dyn | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms generic@number | strict | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms | strict | 76 | 34 | 6 | 9 | 0 | 0 | 27 | 0 |

| UNKNOWN, dyn: first stuck construct | functions | examples |
|---|---|---|
| while/for loop | 19 | `cb_chunkBy`, `cb_unionBy`, `cb_unionWith`, `cb_xorWith` |
| for-of over an array | 19 | `wrapAnsiBg`, `bgBlack`, `bgBlackBright`, `bgBlue` |
| other side condition | 9 | `Semaphore.acquire`, `clamp`, `trimEnd`, `trimStart` |
| external call answer | 6 | `streamToString`, `parseAbortSignal`, `generateCombinations`, `generateAllCombos` |
| dyn operation result (Dyn.typeof, Dyn.eq, Dyn.isArrayTy, Dyn.truthy) not decided | 5 | `isNull`, `isUndefined`, `invariant`, `isNull` |
| cell of a reference below the first level (World.Closed / Val.Live not used) | 5 | `Mutex.get isLocked`, `Mutex.acquire`, `Mutex.release`, `handleStdin` |
| call of a function value | 4 | `cb_partition_3`, `Semaphore.release`, `count<number>`, `head<number>` |
| undecided test on a value read at run time (dyn operation, string comparison) | 4 | `nullishRank`, `eq`, `isNil`, `isNil` |
| undecided test: index from an argument within bounds | 3 | `percentile`, `percentile`, `calculateMedian` |
| heartbeat limit | 3 | `deburr`, `escape`, `unescape` |
| for-of over a string | 3 | `Trie.insertNode`, `Trie.find`, `Trie.searchNode` |
| recursive call | 3 | `factorial`, `nthFibonacciRecursively`, `solve` |
| builtin: reduce without an initial value | 3 | `greatestCommonFactor`, `binaryLCM`, `lowestCommonMultiple` |
| external call answer (ArrayBuffer.isView) | 2 | `isTypedArray`, `isTypedArray` |
| undecided test on string operations | 2 | `stringSize`, `createPadding` |
| expression | 2 | `defaultTo<number, number>`, `isNotNil<number>` |
| call not unfolded (second call, or after the unfolding phase) | 2 | `generateParentheses`, `binomialCoefficient` |
| for-of over a Map | 1 | `hasValue<number, number>` |
| builtin: arrFilter with a callback that captures variables | 1 | `xor<number>` |

The search finds no panic in any PROVED function (cross-check: 226 searches; 215 finished with
300 inputs and 8 more with 100 small ones; 3 did not: `logTwo`, `squareRoot`,
`TreeNode<number>.new`). Of the 96 UNKNOWN dyn functions, 81 were searched without a panic, 6
have argument types the search does not generate (`Iterator` records and host objects:
`cb_partition_3`, `count<number>`, `head<number>`, `handleStdin`, `parseAbortSignal`,
`streamToString`), and for 9 no pass finished (the same 9 as on `562bde2`).

Tactic issue seen (reported, not fixed here): `ts_auto` logs errors from inside, where a failing
`omega` or `simp` should be a discarded attempt: es-toolkit `deburr` (strict: `omega could not
prove the goal`, then the heartbeat limit) and TheAlgorithms `CountSmallerItems` (`simp made no
progress`; residual goal `0 ≤ 2 ^ 53`). Neither changes a verdict (`CountSmallerItems` has a
counterexample).

Cost: 1.37 core-h metered (build, emission and elaboration 0.09; 359 proof files 0.66; search
0.27; Node checks 0.03; cross-check 0.32), the guard logs' core-seconds summed; first given here
as 1.28, a sum of the per-job totals rounded to 0.001 core-h. Proof files took 5 to 164 s each
(300 s cap, never reached); 242 strict attempts take the verdict of an identical dyn attempt, 31
were run.

## Projects

* **es-toolkit** v1.52.0 (`toss/es-toolkit`, commit `32f4c8f`; MIT), the project named in the
  task: a modern lodash replacement, 100% TypeScript, `strict: true`, no runtime dependencies.
  All of `src/` except tests (`*.spec.ts`), including the lodash-compatibility layer
  `src/compat` (367 functions, written against lodash's loose signatures), `src/fp` (curried
  versions) and `src/server` (terminal colours, `exec`).
* **TheAlgorithms/TypeScript** at commit `19b4ced` (no releases; MIT): textbook algorithms and
  data structures written in strict TypeScript (sorts, searches, number theory, dynamic
  programming, graphs, stacks/queues/heaps/tries), i.e. plain functions and small classes over
  arrays, strings, numbers and maps, with many loops: the closest public match to "plain
  functions over arrays, strings, numbers and maps", and the code that exercises loop
  summarization most. All directories except `test/`.
* Not chosen: **date-fns** works on `Date` values, which StrictTS has no model of (only
  `Date.now()` is an oracle), so it measures one missing type; **remeda** dispatches every
  exported function through `purry(impl, args)` with `...args: ReadonlyArray<unknown>` and
  types its implementations with type-fest's type-level programs (a devDependency, TS 6), so it
  measures the type mapper rather than code.

The tsconfigs used (`tools/public/tsconfig/<name>.json`) extend each project's own
`tsconfig.json` (same compiler options) and only select the source files. es-toolkit's
`src/server/exec.ts` imports `node:` modules: their types come from the translator's own
`@types/node` (`typeRoots`), so nothing is installed into the projects; nothing of the projects
is run.

## Method

**Translator modes.** Both modes use the translator of this tree (`frontend/dist`, master
`5044b3c`, which contains `--strict` from `165e1e8`):

* *strict*: `--strict` (`--no-dyn`), the original subset: `unknown` and `any` are rejected;
* *with dyn*: the default, where values of type `unknown` and `any` are the checked dynamic
  type `Ty.dyn` (operations on `any` other than checked casts, property reads and string
  concatenation are rule `any-op`).

(Cross-check: the translator of `93fd4be`, before the dyn change, gives exactly the strict
totals. Master `70e6770`, before the dyn additions `d79e666`/`70d910c`, gave 326 es-toolkit
functions with dyn instead of 329; everything else, the emitted modules included, is identical,
and the proof verdicts of the two tactic versions agree attempt by attempt.)

**Coverage** (`--coverage`): every top-level function, method, constructor, accessor and
module-level arrow is translated on its own; calls of other project functions are assumed
translatable. *Covered* = no subset rule fires in the function; LOC = its non-blank lines.
*Top blockers* list, per rule, the functions it blocks and the functions it alone blocks.

**Emission and elaboration** (`--emit-lean`): the covered functions are translated normally
into one module per project and mode, with everything they call; a function whose body or a
callee's body fails in the normal translator is left out, and generic functions are left out by
design (the IR is monomorphic, and a partial program has no call site that fixes the type
arguments). Each module is elaborated with `lake env lean` (`-DElab.async=false`) and compiled
to an `.olean` for the proof files.

**Generic functions** (`tools/public/mono.js`): for each covered, exported, generic top-level
function or arrow, a one-line wrapper calls it at one instance (each type parameter `T` :=
`number`; `extends PropertyKey` := `string`; other constraints skipped), one wrapper per file;
a coverage run with `--emit-lean` on the wrappers emits the instances (`chunkBy<number>` is
`chunkBy_number`). es-toolkit: 120 wrappers (14 skipped: rest/destructured parameters, one
constrained type parameter), 113 type-check (of the other 7, 4 resolve to a tuple overload, 2
mention a type the wrapper does not import, 1 passes an optional parameter on), 70 are emitted.
TheAlgorithms: its generic code is methods of generic classes (`Stack<T>`, …), which a wrapper
cannot reach; 1 wrapper (`treeSort`).

**Fixed pure callbacks** (`mono.js --callbacks`, `mono_emit.sh dyn NAME cb`): for the covered
functions (generic or not) with a parameter of function type, a wrapper `cb_f` passes one fixed
pure function of that type: `x => x > 0` (predicates on numbers), `x => x !== ''` (on strings),
the identity (numbers to numbers), `x => String(x)` (numbers to strings), a constant otherwise.
This replaces the statement's arbitrary callback (class A below), so the attempt is about the
function's own loop. es-toolkit: 67 wrappers (2 skipped), 65 type-check (2 resolve to a tuple
overload), 47 are emitted; TheAlgorithms has no covered function with a callback parameter.

**Proof attempts** (`tools/public/attempts.py`): for every emitted function whose own IR has a
loop (`for`, `for … of` over arrays, strings, Maps and Sets, `while`, `do … while`) or an array
callback (`reduce`, `reduceRight`, `map`, `filter`, `some`, `every`, `find`, `findIndex`,
`findLast`, `findLastIndex`, `forEach`, `sort`, `flatMap`, `Array.from` with a function,
`Map`/`Set` `forEach`), one theorem

```lean
theorem auto_f (I : Impl) (w : World TT) <arguments> <hypotheses> :
    JS.Returns (callFun I program fRef <arguments>) w := by
  ts_auto
```

with array, `Map`, `Set` and dictionary arguments as allocated cells (`hw : w.heap.get? (.arr T,
a) = some c`, `hn : a < w.next`, and `hs : c.size < 2 ^ 32` for arrays), string arguments,
string fields and the elements of string arrays bounded as ECMA-262 §6.1.4 bounds every String
(`hl : v.toStr.length < 2 ^ 53`, `hl : ∀ x ∈ c.toList, x.toStr.length < 2 ^ 53`; the string
counterpart of `hs`; since 2026-10-24, one helper `str_hyps` in `attempts.py` shared with the
tactic side), object arguments
(`this`) as allocated cells with every field initialised (array/Map/Set/dictionary fields again
allocated cells), and other arguments arbitrary values. `maxHeartbeats 400000`; six attempts per
file, each file one guarded job (5 to 61 s). An attempt is PROVED when Lean reports no error in
it and `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`. Attempts run on
the dyn modules; the *strict* column counts the attempts whose IR has no `dyn` value (they are
translated identically in strict mode). Generic instances already attempted as non-generic
functions are not repeated. The `cb_` wrappers are attempted when the code they reach (their
callees, transitively) has a loop or a callback, and are classified by that code
(`attempts.py --select-prefix cb_`).

**Failure classes** (`tools/public/results.py`, first match wins). Four classes say that the
statement itself is false for some arguments or worlds, so the failure is not the tactic's:

* **A** a parameter of function type: the statement quantifies over every callback, and an
  arbitrary function may throw or diverge;
* **B** an explicit `throw` in the function (argument validation: `max([])`, `trimEnd(s, "ab")`,
  `isPrime(-1)`): reachable for some arguments by design;
* **N** an argument holds a reference that the statement gives no cell (the inner arrays of a
  `number[][]` graph, the nodes of a tree held in a field): in worlds where it dangles, reading it
  panics;
* **M** an input found by reading the code (listed below): a loop bounded by a number argument
  (`n = Infinity`), an index taken from an argument (`start = -1`), `NaN` in a search or sort, an
  empty array read at index 0, a `Math.random()` oracle value outside `[0, 1)`.

The other classes are what `ts_auto` does not handle, from the IR of the function: **C**
`while`/`do … while` (`ts_auto` is invariant- and variant-free, so it has no termination
argument; `ts_while` needs a variant); **D** a counted loop whose condition is not exactly
`i < xs.length` or `i < constant` (`i < xs.length - 1`, `i < Math.sqrt(n)`, a backwards loop); **F**
nested or several loops; **G** `return`/`break` inside the loop body; **H** allocation in the loop
body; **J** a call of a project function in the loop body; **E** a `for … of` over a `Map`/`Set`
with none of these; **K** none of these (inspected below). The translator's own `split`
implementation (`String.prototype.split`, emitted with the module) is not attempted.

## Coverage

The tables are at `5044b3c`. Later translators (same projects, functions covered, strict / dyn):
at `2e3c32d` and through 10-24's dictionaries with named properties (`41679b8`), es-toolkit
234 / 365 and TheAlgorithms 165 / 170; with regular expressions as values (`b7de06f`), es-toolkit
236 / 367 (`createPadding` and `stringSize`, which keep a regex in a variable), TheAlgorithms
unchanged.

### es-toolkit v1.52.0

| mode | functions covered | LOC covered | TS errors |
|---|---|---|---|
| strict | 230/794 (29.0%) | 1509/9427 (16.0%) | 0 |
| dyn | 329/794 (41.4%) | 2296/9427 (24.4%) | 0 |

| directory | functions | strict: functions | strict: LOC | dyn: functions | dyn: LOC |
|---|---|---|---|---|---|
| `src/compat` | 367 | 46 (12.5%) | 288/5094 (5.7%) | 108 (29.4%) | 723/5094 (14.2%) |
| `src/fp` | 104 | 38 (36.5%) | 301/901 (33.4%) | 54 (51.9%) | 490/901 (54.4%) |
| `src/array` | 68 | 35 (51.5%) | 271/720 (37.6%) | 37 (54.4%) | 301/720 (41.8%) |
| `src/server` | 54 | 48 (88.9%) | 159/236 (67.4%) | 49 (90.7%) | 162/236 (68.6%) |
| `src/predicate` | 37 | 0 (0.0%) | 0/390 (0.0%) | 12 (32.4%) | 59/390 (15.1%) |
| `src/object` | 28 | 0 (0.0%) | 0/570 (0.0%) | 0 (0.0%) | 0/570 (0.0%) |
| `src/function` | 26 | 4 (15.4%) | 6/327 (1.8%) | 4 (15.4%) | 6/327 (1.8%) |
| `src/string` | 24 | 15 (62.5%) | 107/209 (51.2%) | 17 (70.8%) | 153/209 (73.2%) |
| `src/math` | 14 | 9 (64.3%) | 71/127 (55.9%) | 9 (64.3%) | 71/127 (55.9%) |
| `src/bigint` | 13 | 9 (69.2%) | 104/151 (68.9%) | 9 (69.2%) | 104/151 (68.9%) |
| `src/iterator` | 13 | 1 (7.7%) | 12/313 (3.8%) | 1 (7.7%) | 12/313 (3.8%) |
| `src/map` | 12 | 11 (91.7%) | 99/117 (84.6%) | 11 (91.7%) | 99/117 (84.6%) |
| `src/promise` | 11 | 5 (45.5%) | 22/97 (22.7%) | 5 (45.5%) | 22/97 (22.7%) |
| `src/set` | 9 | 8 (88.9%) | 62/80 (77.5%) | 8 (88.9%) | 62/80 (77.5%) |
| `src/_internal` | 7 | 1 (14.3%) | 7/51 (13.7%) | 4 (57.1%) | 23/51 (45.1%) |
| `src/util` | 5 | 0 (0.0%) | 0/38 (0.0%) | 1 (20.0%) | 9/38 (23.7%) |
| `src/error` | 2 | 0 (0.0%) | 0/6 (0.0%) | 0 (0.0%) | 0/6 (0.0%) |

Without the lodash-compatibility layer (`src/compat`, 367 functions), es-toolkit is 184/427
functions (43.1%) strict and 221/427 (51.8%) with dyn.

Top blockers (rule: functions blocked / functions it alone blocks):

* strict: `no-any` 366/3, `any-type` 353/19, `unsupported-type` 121/24, `no-loose-eq` 114/20,
  `no-symbol` 105/6, `no-object-type` 98/10, `unsupported-builtin` 97/10, `as-downcast` 91/8,
  `fn-type-rest` 71/1, `unsupported` 43/2
* dyn: `unsupported-type` 125/42, `no-loose-eq` 114/34, `no-symbol` 113/17, `as-downcast` 96/14,
  `no-object-type` 90/21, `unsupported-builtin` 78/14, `fn-type-rest` 71/27, `unsupported`
  36/3, `any-op` 36/4, `unsupported-conversion` 29/3

`unknown`/`any` are the dominant blockers of the strict subset (most of them in `src/compat`
and `src/predicate`, whose functions take `unknown` or `any` by design); with dyn, no single rule
dominates: unsupported types (mapped/conditional object types, `Capitalize<T>`), `==`, symbols,
downcasts and the `object`/`{}` types.

### TheAlgorithms/TypeScript 19b4ced

| mode | functions covered | LOC covered | TS errors |
|---|---|---|---|
| strict | 163/234 (69.7%) | 1529/2635 (58.0%) | 7 |
| dyn | 166/234 (70.9%) | 1561/2635 (59.2%) | 7 |

| directory | functions | strict: functions | strict: LOC | dyn: functions | dyn: LOC |
|---|---|---|---|---|---|
| `data_structures` | 123 | 91 (74.0%) | 708/945 (74.9%) | 93 (75.6%) | 734/945 (77.7%) |
| `maths` | 50 | 35 (70.0%) | 303/583 (52.0%) | 35 (70.0%) | 303/583 (52.0%) |
| `sorts` | 23 | 17 (73.9%) | 193/289 (66.8%) | 17 (73.9%) | 193/289 (66.8%) |
| `graph` | 17 | 5 (29.4%) | 58/418 (13.9%) | 5 (29.4%) | 58/418 (13.9%) |
| `search` | 8 | 6 (75.0%) | 144/171 (84.2%) | 7 (87.5%) | 150/171 (87.7%) |
| `bit_manipulation` | 4 | 4 (100.0%) | 33/33 (100.0%) | 4 (100.0%) | 33/33 (100.0%) |
| `dynamic_programming` | 3 | 0 (0.0%) | 0/102 (0.0%) | 0 (0.0%) | 0/102 (0.0%) |
| `other` | 3 | 3 (100.0%) | 45/45 (100.0%) | 3 (100.0%) | 45/45 (100.0%) |
| `backtracking` | 2 | 2 (100.0%) | 45/45 (100.0%) | 2 (100.0%) | 45/45 (100.0%) |
| `ciphers` | 1 | 0 (0.0%) | 0/4 (0.0%) | 0 (0.0%) | 0/4 (0.0%) |

Top blockers:

* strict: `any-type` 25/16, `no-loose-eq` 15/12, `no-extends` 12/7, `mixed-compare` 6/3,
  `unsupported-builtin` 5/2, `unsupported-type` 4/1, `no-any` 4/0, `no-generators` 3/0,
  `as-downcast` 2/2, `unsupported` 2/1
* dyn: `unsupported-conversion` 16/10, `no-loose-eq` 15/12, `no-extends` 12/7,
  `unsupported-builtin` 7/4, `mixed-compare` 6/3, `any-op` 5/1, `unsupported-type` 4/1,
  `unsupported` 3/1, `no-generators` 3/0, `as-downcast` 2/2

The 7 TS errors are one file that does not type-check upstream either
(`data_structures/set/map_set.ts` imports `./map`, which is in another directory). With dyn,
the 25 `any-type` functions become 3 covered functions and 16 `unsupported-conversion` ones
(`any` values used as numbers or arrays: `coinChange`, `knapsack`, `bellmanFord`, …);
`linearSearch(array: any[], target: any)` and two `Heap` methods become covered.

## Emitted modules

| module | covered | generic (left out by design) | emitted | left out (body or callee fails) | Lean lines | elaboration |
|---|---|---|---|---|---|---|
| es-toolkit strict | 230 | 112 | 72 | 25 failed, 30 needing them | 1,322 | 0 errors |
| es-toolkit dyn | 329 | 134 | 102 | 49 failed, 76 needing them | 1,846 | 0 errors |
| es-toolkit generic wrappers (dyn) | 113 wrappers | | 70 wrappers | 37 failed, 57 needing them | 2,493 | 0 errors |
| es-toolkit pure-callback wrappers (dyn) | 65 wrappers | | 47 wrappers | 12 failed, 21 needing them | 1,802 | 0 errors |
| TheAlgorithms strict | 163 | 87 | 72 | 3 failed, 4 needing them | 1,924 | 0 errors |
| TheAlgorithms dyn | 166 | 89 | 73 | 3 failed, 4 needing them | 1,949 | 0 errors |
| TheAlgorithms generic wrappers (dyn) | 1 wrapper | | 1 | | 176 | 0 errors |

("failed"/"needing them" count functions, callees included.) Every module elaborates without
an error, each in at most 11 s of wall time on one core. The "failed" functions are covered in
coverage mode because coverage assumes callees translatable; in the normal translation a callee
fails (es-toolkit dyn on master `70e6770`, rules of the failing bodies: `unsupported-builtin`
10, `no-symbol` 9, `unsupported` 8, mostly function overloads such as `randomInt`, `instanceof`
7, `no-regexp` 6 for regular-expression constants, `no-loose-eq` 6, `any-op` 6).

## Automatic proofs

**`JS.Returns` is too strong as a uniform statement.** It says that the function terminates
normally for every argument and every world. Functions that validate their arguments throw on
purpose (`max([])`, `isPrime(-1)`, `trimEnd(s, "ab")`), so for them the statement is false by
design; so it is for higher-order functions over arbitrary callbacks, for loops bounded by a
number argument (`n = Infinity`), for indices taken from arguments, and for references the
statement leaves without a cell. 72 of the 95 attempts are such false statements (classes A, B,
N, M). The automatic-proof rate is therefore given over the attempts whose statement may be true
(the other 23); the right statements for the rest are `JS.Returns` under a precondition (the
validation's condition, the callback's contract, finite in-range numbers, allocated inner cells)
or the weaker `JS.NoPanic`/`JS.NoFault` (`StrictTS/Proof/Contract.lean`).

| functions | attempts | PROVED | statement false for some input (A, B, N, M) | statement may be true | PROVED / may be true | strict: may be true | strict: PROVED |
|---|---|---|---|---|---|---|---|
| es-toolkit | 12 | 3 | 7 | 5 | 3/5 (60%) | 5 | 3 |
| es-toolkit generic@number | 39 | 2 | 34 | 5 | 2/5 (40%) | 5 | 2 |
| TheAlgorithms | 42 | 0 | 30 | 12 | 0/12 (0%) | 11 | 0 |
| TheAlgorithms generic@number | 2 | 0 | 1 | 1 | 0/1 (0%) | 1 | 0 |
| es-toolkit with fixed pure callbacks | 47 | 23 | 3 | 44 | 23/44 (52%) | 42 | 22 |

Per project, over the attempts whose statement may be true: **es-toolkit 5/10** (3 loops and 2
curried functions that only return a closure) with arbitrary arguments, and **23/44 (52%)** for
its callback functions with one fixed pure callback (14 loops, 9 curried functions);
**TheAlgorithms 0/13**. The strict columns count the attempts whose IR has no `dyn` value.

| verdict / class | es-toolkit | es-toolkit generic@number | TheAlgorithms | TheAlgorithms generic@number | es-toolkit pure callbacks | examples |
|---|---|---|---|---|---|---|
| proved | 3 | 0 | 0 | 0 | 14 | `sum`, `reverseString`, `sum` (bigint); `countBy`, `keyBy`, `mapValues`, `sumBy`, `uniqBy` |
| proved (returns a function: the loop is not run) | 0 | 2 | 0 | 0 | 9 | curried `fp` versions: `findIndex`, `chunkBy`, `takeRightWhile` |
| *statement false:* A callback parameter | 0 | 33 | 0 | 0 | 0 | `chunkBy`, `countBy`, `sumBy`, `uniqBy`, `keyBy` |
| *statement false:* B explicit throw | 7 | 0 | 11 | 0 | 3 | `percentile`, `trimEnd`, `max`, `findMin`, `isPrime`; `maxBy`, `medianBy` |
| *statement false:* N dangling reference | 0 | 0 | 6 | 1 | 0 | `dfs`, `gatherScc` (`number[][]` graphs), `Trie.insertNode`, `BinarySearchTree.insert` |
| *statement false:* M input from the code | 0 | 1 | 13 | 0 | 0 | `logTwo`, `gnomeSort`, `sentinelSearch`, `shuffle` (list below) |
| C `while` loop | 1 | 0 | 4 | 0 | 0 | `dedentImpl`, `addBinary`, `isPalindrome`, `insertionSort` |
| D counted loop bound not `i < xs.length` / constant | 0 | 0 | 6 | 0 | 2 | `isSortedArray`, `bubbleSort`, `isPerfectNumber`, `dropRightWhile` |
| F nested or several loops | 0 | 0 | 1 | 0 | 0 | `selectionSort` |
| G `return`/`break` inside the loop | 0 | 1 | 1 | 0 | 11 | `hasValue`, `linearSearch`; `every`, `some`, `findKey`, `takeWhile` |
| H loop body allocates | 0 | 0 | 0 | 0 | 1 | `chunkBy` |
| J loop body calls a project function | 0 | 0 | 0 | 1 | 0 | `treeSort` |
| K other | 1 | 2 | 0 | 0 | 7 | `median`, `difference`, `intersection`; `differenceWith`, `meanBy` |

Class M, the inputs (found by reading the code; each makes the run diverge, panic on an
out-of-bounds read, or never sort): `logTwo(-1)` (`-1 >> 1 === -1`), `armstrongNumber(Infinity)`
(`Math.floor(Infinity / 10) === Infinity`), `jugglerSequence(a, Infinity)`, `pascalsTriangle(0)`
(reads `arr[-1]`), `binarySearchIterative(xs, t, -1)` (reads `array[-1]`),
`interpolationSearch([], t)` and `fibonacciSearch([], t)` (read index 0 of an empty array),
`sentinelSearch(xs, NaN)` (the scan passes the sentinel), `gnomeSort([NaN, 1])` (swaps forever),
`partition(xs, -5)` and `CountSmallerItems(xs, -5, x)` (negative indices), `bogoSort([2, 1])` with
`Math.random()` always `0.99` (never sorted), and `shuffleArray`/es-toolkit `shuffle` with
`Math.random() = 1` (index `i + 1`): the world's random oracle is any double, as in the semantics.

Reading the table:

* With arbitrary arguments, the proved functions are the loops `ts_auto` was built for: `sum`
  (`for (let i = 0; i < nums.length; i++) result += nums[i]`, number and bigint) and
  `reverseString` (`for … of` over a string building a string), for every array or string and
  every world.
* Of the 18 failures whose statement may be true, 5 are `while` loops (C: no termination
  argument by design), 6 counted loops outside the summarizable form (D: `ts_summarize` folds
  `for (let i = k0; i < n; i++)` only for `n` an array length or a constant), 1 nested loop, 2
  early returns, 1 call in a loop body and 3 others.
* With one fixed pure callback instead of an arbitrary one, 23 of the 47 callback functions of
  es-toolkit are proved: 14 loops (`countBy`, `keyBy`, `mapKeys`, `mapValues`, and `filter`,
  `forEach`, `map` over Maps and Sets; `sumBy` twice; `uniqBy`) and 9 curried `fp` versions. The
  rest: 11 early exits inside loops (`every`/`some`/`find`/`findKey`/`findValue` over Maps and
  Sets, `takeWhile`'s `break`, `uniqWith`, `unionWith`, `xorWith`), 3 validation throws (`maxBy`,
  `minBy`, `medianBy` on an empty array), 2 backwards loops (`for (let i = arr.length - 1; i >= 0;
  i--)`: `dropRightWhile`, `takeRightWhile`), 1 allocation in the loop body (`chunkBy`), and 7
  others: callbacks nested in callbacks (`differenceWith`: `filter(x => ys.every(y =>
  !eq(x, y)))`, `intersectionWith`, `isSubsetWith`), a callback forwarded through a closure
  (`meanBy`: `sumBy(items, item => getValue(item)) / items.length`; `medianBy`), `unionBy`,
  `dropWhile`.
* The K cases of the first sets, inspected: `median` (`nums.slice().sort((a, b) => a - b)` then
  `sorted[floor(n / 2)]`): the `sort` on the fresh copy stays unsummarized behind the undecided
  `nums.length === 0` test; `difference`/`intersection` (`xs.filter(x => !set.has(x))`):
  `ts_callbacks` does not rewrite a callback whose closure captures a heap reference (the `Set`).

**Validating functions under `JS.NoPanic`.** For the 21 functions of class B, the statement that
may hold is `JS.NoPanic` (no panic; throwing and diverging are allowed). `ts_auto` proves none
of them: 0/21 (2 have a dangling `chars` array: `trimEnd`, `trimStart`; 19 may be true). In the
residual goals the validation test (`nums.length === 0`) stays undecided and the loop after it
unsummarized (problem (1) below); besides, 7 of TheAlgorithms' have counted loops bounded by a
number (`for (let i = 2; i <= Math.sqrt(num); i++)`) and 2 `while` loops, for which `ts_auto` has no
rule even in partial correctness.

| functions (`JS.NoPanic`) | attempts | PROVED | statement may be true | PROVED / may be true |
|---|---|---|---|---|
| es-toolkit, class B | 7 | 0 | 5 | 0/5 |
| es-toolkit with fixed pure callbacks, class B | 3 | 0 | 3 | 0/3 |
| TheAlgorithms, class B | 11 | 0 | 11 | 0/11 |

### Split before summarizing (branch autosplit, 2026-10-24)

`ts_auto` now splits on the innermost undecided test of the goal before summarizing, so a loop
or callback after an argument validation is summarized in the case where the validation passes,
and it splits the same way in its final step when `split` and `simp_all` fail (straight-line
code after a validation); see `StrictTS/Proof/Auto.lean`. The attempts above were rerun on the
same emitted modules (translator of master `c322233`, emitted again on 2026-10-24) with the
tactics of master `c322233` and of autosplit `29c1149`, each built in a frozen copy of its tree:

| attempts | `c322233` | `29c1149` | newly proved |
|---|---|---|---|
| `JS.Returns`, es-toolkit (16, and 39 generic instances) | 3 + 2 | 3 + 2 | |
| `JS.Returns`, es-toolkit with fixed pure callbacks (47) | 23 | 25 | `cb_dropWhile`, `cb_meanBy` |
| `JS.Returns`, TheAlgorithms (44, and 2 generic instances) | 0 | 0 | |
| `JS.NoPanic`, class B, es-toolkit (7) | 0 | 2 | `max`, `min` (bigint) |
| `JS.NoPanic`, class B, es-toolkit with fixed pure callbacks (3) | 0 | 2 | `maxBy`, `minBy` |
| `JS.NoPanic`, class B, TheAlgorithms (11) | 0 | 2 | `calculateMean`, `findMin` |

No attempt that `c322233` proves fails with `29c1149`. The class-B `JS.NoPanic` attempts go from
0/21 to 6/21 (6/19 of those whose statement may be true). Of the 15 that fail: 9 TheAlgorithms
loops have no summary (7 counted loops with another bound or step: `i <= Math.sqrt(num)`,
`i <= num / 2`, `i * i <= num`, `i < str1.length`, `i -= 2`; 2 `while` loops),
2 read a dangling `chars` array (class N: `trimEnd`, `trimStart`), and 4 index a sorted copy at
`Math.floor(n / 2)` or `Math.ceil(n * p / 100) - 1` (`median`, `percentile` ×2, `medianBy`), which
needs reasoning on rounded doubles. The proof files take longer: 730 s for the 32 files against
463 s (the largest increase in the es-toolkit `JS.NoPanic` file, 129 s against 46 s, where the
failing attempts split on several tests); every file stays under 590 s. The equivalence benchmark (`tests/equiv-bench`, run in
three subsets with `--only`) gives the same verdict on every pair under both trees: 30/44
equivalences proved, 23/23 differences refuted, no wrong verdict (Lean phase 337 s against
460 s).

## Uniform NoPanic (master `562bde2`, six functions on `9e56ea6`; earlier runs on `2e3c32d` and `70f729b`, 2026-10-24)

**Summary.** On master `562bde2`, `ts_auto` alone proves one statement for every emitted
function, `JS.NoPanic` (the run never panics: it never reaches a place where TypeScript's types
are unsound or the model stops; it may return, throw or diverge): es-toolkit 118 of 164 functions
(72%) in the strict subset and 138 of 209 (66%) with dyn, TheAlgorithms 35 of 82 (43%) and 35 of
83 (42%); on `2e3c32d` they were 108/162, 128/207, 32/82 and 32/83. Six functions that `562bde2`
translates with a bug (`s[i]` on a string, see below) take their verdicts from master `9e56ea6`,
which fixes it: TheAlgorithms `hammingDistance` is proved; es-toolkit `deburr`, `dedentImpl`,
`trimEnd`, `trimStart` and TheAlgorithms `parseNestedBrackets` are UNKNOWN; none has a
counterexample. A search with random and edge-value inputs through the executable semantics,
each panicking input replayed on the original TypeScript in Node, gives 26 counterexamples with
dyn (16 strict): 7 latent bugs, 9 reads outside an array that the code tolerates, and 10 model
limitations; it finds no panic in any proved function. The 7 latent bugs: es-toolkit
`sample([])` returns `undefined` at type `T`; in TheAlgorithms, `pascalsTriangle(NaN)` returns
`undefined` at type `number[]`, `sentinelSearch(xs, NaN)` never ends, `QuickSort` and
`QuickSelect` throw on index arguments outside the array, and the Kosaraju helpers
`getNodePriorities` and `gatherScc` throw on a node outside the graph.

**With host specifications** (a separate result; the numbers above use none). Two facts that
ECMA-262 fixes about the host's answers, used as hypotheses: `w.MatchAllFresh` (`String.prototype.
matchAll` answers a fresh array of matches, §22.1.3.14) and `w.MatchElementZero` (element 0 of a
match is a string, §22.2.7.2), both `World.ExtSpec` instances that still allow errors
(`StrictTS/Proof/Extern.lean`; emitted by `nopanic.py --ext-specs` for the code that reaches these
externs). On master `9e56ea6`, as on `883a989`, of the 23 attempts that reach them (strict and
dyn alike), 20 are proved with the two hypotheses against 2 without (`bgAnsi256` and `bgRgb`,
which only return a function): the 18 colour functions, `wrapAnsiBg` and TheAlgorithms
`XORCipher`; `bgHex`, `escape` and `unescape` stay UNKNOWN (they need es-toolkit's module facts).
Without the hypotheses the 23 have the verdicts and first stuck constructs of `562bde2`.

| project | mode | attempts, 2e3c32d | attempts, 562bde2 | PROVED, 2e3c32d | PROVED, 562bde2 | COUNTEREXAMPLE, 2e3c32d | COUNTEREXAMPLE, 562bde2 (latent bug / tolerated / limitation) | UNKNOWN, 2e3c32d | UNKNOWN, 562bde2 |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit | strict | 162 | 164 | 108 (67%) | 118 (72%) | 1 (1/0/0) | 1 (1/0/0) | 53 | 45 |
| es-toolkit | dyn | 207 | 209 | 128 (62%) | 138 (66%) | 11 (1/0/10) | 11 (1/0/10) | 68 | 60 |
| TheAlgorithms | strict | 82 | 82 | 32 (39%) | 35 (43%) | 18 (6/12/0) | 15 (6/9/0) | 32 | 32 |
| TheAlgorithms | dyn | 83 | 83 | 32 (39%) | 35 (42%) | 18 (6/12/0) | 15 (6/9/0) | 33 | 33 |

Attempts are matched by set, source name and signature. The `562bde2` columns take the six `s[i]`
functions and `trim` from `9e56ea6`; in the `2e3c32d` columns, the published counts, the six are
UNKNOWN (the bug was there too, and none of them was proved). What changed from `2e3c32d` to
`562bde2` (the same in strict and dyn):

* New proofs (13): TheAlgorithms `isSortedArray`, `nthFibonacciUsingFormula`, `hammingDistance`
  (on `9e56ea6`, see below); es-toolkit fixed-callback wrappers `cb_every`, `cb_some`,
  `cb_find_2`, `cb_findKey`, `cb_findValue`, `cb_every_2`, `cb_some_2` (`for … of` over Maps and
  Sets with an early `return`), `cb_takeWhile` (a counted loop with `break`), `cb_dropRightWhile`,
  `cb_takeRightWhile` (backwards loops).
* Lost proofs: none. New counterexamples: none.
* Counterexamples gone: `Trie.find`, `Trie.insertNode`, `Trie.searchNode` (tolerated reads). The
  translator now reads a dictionary read that the code tests for truthiness as an optional read
  (frontend `7ab6385`), so the model no longer panics where JavaScript gives `undefined`; the
  attempts are UNKNOWN (first stuck construct: the `for … of` over the word).
* New attempts: es-toolkit `createPadding` and `stringSize`, emitted by the new translator:
  UNKNOWN (module variable cell: the `ModuleInit` facts are not derived).
* The six `s[i]` functions, run on `9e56ea6`: es-toolkit `deburr`, `dedentImpl` (strict and
  dyn), `trimEnd`, `trimStart` (dyn); TheAlgorithms `hammingDistance`, `parseNestedBrackets`. At
  `562bde2` the translator gives string indexing `s[i]` the semantics of `.at` (`s[-1]`, `s[1.5]`,
  `s[NaN]` give characters where JavaScript gives `undefined`; soundness finding of 10-24);
  `9e56ea6` reads a code unit only at an array index (frontend `7eec842`). The emitted modules of
  the two commits differ only in these reads, so the attempts whose code changed are those of the
  six functions and of es-toolkit `trim`, which calls `trimEnd` and `trimStart` (compared by the
  hash of each attempt's code; the generic and callback wrappers are identical). Verdicts on
  `9e56ea6`, the same as on `562bde2` except where noted: `hammingDistance` PROVED (two strings
  indexed by one counter, under the string bounds; it reads `s[i]` only below both lengths);
  `deburr` and `dedentImpl` UNKNOWN at a `while`/`for` loop; `trimEnd`, `trimStart` and `trim`
  UNKNOWN at a residual condition; `parseNestedBrackets` UNKNOWN, now at the heartbeat limit (with
  4x the limit, `ts_auto` ends at the counted loop over the string where it stopped on `562bde2`).
  The search finds no panic in any of them (300 inputs each, every pass finished).

The earlier runs, the published `2e3c32d` numbers against the first run:

| project | mode | attempts | PROVED, 70f729b | PROVED, 2e3c32d | COUNTEREXAMPLE | UNKNOWN, 70f729b | UNKNOWN, 2e3c32d |
|---|---|---|---|---|---|---|---|
| es-toolkit | strict | 162 | 103 (64%) | 108 (67%) | 1 | 58 | 53 |
| es-toolkit | dyn | 207 | 123 (59%) | 128 (62%) | 11 | 73 | 68 |
| TheAlgorithms | strict | 82 | 31 (38%) | 32 (39%) | 18 | 33 | 32 |
| TheAlgorithms | dyn | 83 | 31 (37%) | 32 (39%) | 18 | 34 | 33 |

Proved on `2e3c32d` only: es-toolkit `median` (the number and the bigint version), `cb_medianBy`,
`cb_medianBy_2`, `union<number>`, and TheAlgorithms `findFactors` (strict and dyn alike). Proved on
`70f729b` only: none. No proved function has a counterexample. Between the two commits only the
tactics changed (`StrictTS/Proof`), so the emitted modules, the semantics and the counterexamples
are the same.

**Statement.** For every function of the emitted modules, not only those with loops:
`JS.NoPanic (callFun I program fRef args) w := by ts_auto`. A panic is where TypeScript's types are
unsound and the model stops (an out-of-bounds read typed `T`, a missing dictionary key read as
`T`, `x!` on `undefined`) or a construct the model does not cover. Everything is measured on
git-archive copies of master (translator, library and tactics; built in `scratch/base_70f729b`,
`scratch/base_2e3c32d`, `scratch/base_562bde2` and `scratch/base_9e56ea6`), for the emitted
modules of both projects in both modes, with the generic functions at `T := number` and the
higher-order functions with one fixed pure callback (`cb_*`). The sections above use `5044b3c`.
From `70f729b` to `2e3c32d` only the tactics changed; from `2e3c32d` to `562bde2` also the
translator (truthiness reads, identity boxes, regular expressions as values, dictionaries,
emission fixes) and the string library's case-mapping tables, so the modules were emitted again
and the counterexample search redone. On `9e56ea6` the modules were emitted again and differ
from those of `562bde2` only in the `s[i]` reads, so only the seven functions whose code changed
were run there, with the 23 regex attempts; the other attempts keep their `562bde2` verdicts
(the tactics changed as well, by a `JS.NoPanic` fallback for `for … of` loops, `9785682`).
The coverage that decides what is emitted: es-toolkit strict 236/794 functions (29.7%), dyn
367/794 (46.2%) at `562bde2` and `9e56ea6` (234 and 365 at the earlier commits); TheAlgorithms
strict 165/234 (70.5%), dyn 170/234 (72.6%) at all four.

**Hypotheses.** As in the attempts above (argument arrays, Maps, Sets and dictionaries are
allocated cells; objects are allocated with every field initialised). New, for references below
the first level (class N above: the inner arrays of a `number[][]`, objects held in fields,
references inside optional, union, tuple, record or `unknown` arguments): `w.Closed` (every
reference stored in the heap names a cell, `StrictTS/Proof/Contract.lean`) and `Val.Live w v`
for each such argument; `w.ModuleInit I program` when the code reads a module variable; and
the string bounds `(hl : v.toStr.length < 2 ^ 53)` of the attempts above (string arguments, string
fields, elements of string arrays). No statement is false by construction any more, except for
functions with a callback parameter (a callback may panic): those are attempted through their
`cb_*` wrappers instead.

**Verdicts.**

* PROVED: by `ts_auto` alone, standard axioms only, within `maxHeartbeats 1000000` (5x Lean's
  default; the `562bde2` files carry the limit and none reaches it, nor any `9e56ea6` file but
  `parseNestedBrackets`'s; the earlier runs used the default, and the attempts that reached it, 4
  on `70f729b` and 15 on `2e3c32d`, were run again with the higher limit: one more proof,
  `cb_medianBy_2` on `2e3c32d`; an attempt that stays under a limit runs the same under any higher
  one, and a full rerun of the 302 `2e3c32d` files written with the limit gives the same verdicts
  and the same first stuck constructs).
* COUNTEREXAMPLE: the search (`tools/public/lean/PanicSearch.lean`) runs the function through
  the executable semantics (`#eval`, as `StrictTS.Testing` does) on 300 random and edge-value inputs
  (NaN, ±0, ±Infinity, random bit patterns, astral and lone-surrogate strings, the property names
  of `Object.prototype`, `unknown` values including host objects) in the initialised module world,
  with the argument cells allocated as the hypotheses require and `Math.random()` in [0, 1); a
  second pass with small numbers covers functions whose loops a large argument makes run too
  long. The first panicking input is run on the original TypeScript in Node (`tools/public/node`:
  the project transpiled with a check on every read whose type excludes `undefined` (index out of
  bounds, missing key, `x!`, uninitialised field), run under Node's permission model). **Latent
  bug**: Node reaches a value the types exclude and, with the checks off, that value escapes: the
  result is outside the declared return type, the run throws, or it does not end. **Unsound read
  tolerated**: Node reaches such a value but the code copes with it (the result stays in its
  declared type). **Model limitation**: Node runs the input within the types.
* UNKNOWN: neither; the first stuck construct of the goal that `ts_auto` leaves is reported
  (`np_stuck`, `tools/public/lean/NoPanicDiag.lean`).

A strict attempt whose code (the function, its callees, the classes it mentions, and the module
body when it reads module variables) is identical to a dyn attempt takes the dyn verdict (234 of
246 at `562bde2`, 232 of 244 before); the others were run (12, all PROVED at every commit). Proof
runs at `562bde2`: one file per attempt, 304 files, 5 to 123 s each (300 s cap, never reached);
the whole re-measure (emission, proofs, search, Node checks, cross-check) metered 1.34 core-h; the
recheck on `9e56ea6` (build, emission, 7 files for the attempts whose code changed, the 46 regex
files, the searches and the run at 4x the heartbeat limit) 0.37 core-h. The string bounds were added after
the first `70f729b` run: the 66 attempts whose statement they change were run again and gave the
same verdicts.

Tables for `562bde2`, with the six `s[i]` functions and `trim` from `9e56ea6`:

| project | mode | attempts | PROVED | COUNTEREXAMPLE | UNKNOWN | PROVED or COUNTEREXAMPLE |
|---|---|---|---|---|---|---|
| es-toolkit | strict | 164 | 118 (72%) | 1 | 45 | 119 (73%) |
| es-toolkit | dyn | 209 | 138 (66%) | 11 | 60 | 149 (71%) |
| TheAlgorithms | strict | 82 | 35 (43%) | 15 | 32 | 50 (61%) |
| TheAlgorithms | dyn | 83 | 35 (42%) | 15 | 33 | 50 (60%) |

| functions | mode | attempts | PROVED | COUNTEREXAMPLE: latent bug | unsound read tolerated | model limitation | Node inconclusive | UNKNOWN | not attempted (callback parameter) |
|---|---|---|---|---|---|---|---|---|---|
| es-toolkit fixed callbacks | dyn | 47 | 39 | 0 | 0 | 0 | 0 | 8 | 0 |
| es-toolkit fixed callbacks | strict | 45 | 38 | 0 | 0 | 0 | 0 | 7 | 0 |
| es-toolkit | dyn | 139 | 83 | 0 | 0 | 10 | 0 | 46 | 0 |
| es-toolkit generic@number | dyn | 23 | 16 | 1 | 0 | 0 | 0 | 6 | 47 |
| es-toolkit generic@number | strict | 22 | 16 | 1 | 0 | 0 | 0 | 5 | 45 |
| es-toolkit | strict | 97 | 64 | 0 | 0 | 0 | 0 | 33 | 0 |
| TheAlgorithms | dyn | 77 | 33 | 6 | 9 | 0 | 0 | 29 | 0 |
| TheAlgorithms generic@number | dyn | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms generic@number | strict | 6 | 2 | 0 | 0 | 0 | 0 | 4 | 0 |
| TheAlgorithms | strict | 76 | 33 | 6 | 9 | 0 | 0 | 28 | 0 |

The search finds no panic in any PROVED function (cross-check at `562bde2`: 185 runs; 174 searches
of 300 inputs finished; 11 did not, because some inputs make the function run on, which
`JS.NoPanic` allows: e.g. `logTwo(-1)`, `jugglerSequence(a, Infinity)`; `hammingDistance` on
`9e56ea6`: 300 inputs). Of the 93 UNKNOWN dyn functions, 83 were searched without a panic (300
inputs, or 100 small ones), 1 has argument types the search does not generate (`streamToString`),
and for 9 no pass finished (`bogoSort`, `gnomeSort` on `[NaN, 1]`, recursion on negative
arguments, `BinarySearchTree` traversals).

**Counterexamples** (`562bde2`, dyn; the strict ones are the same functions, without the
`unknown` predicates). Inputs are JavaScript literals.

| latent bug (dyn) | API | input | Lean panic | Node, with checks | Node, checks off |
|---|---|---|---|---|---|
| `QuickSelect` | exported | `[[31, 122851254, -23], -0, NaN, -488]` | array read at a non-index key | violation: `sorts/quick_sort.ts:14:17 array[pivotIndex]` | threw (RangeError: Maximum call stack size exceeded) |
| `QuickSort` | exported | `[[5.694854281447043e-181, -0, 172, -160, 3664979655], -0,...` | array read at a non-index key | violation: `sorts/quick_sort.ts:14:17 array[pivotIndex]` | threw (RangeError: Invalid array length) |
| `pascalsTriangle` | exported | `[NaN]` | array read at a non-index key | violation: `maths/pascals_triangle.ts:39:10 arr[arr.length - 1]` | returned `undefined` (declared `number[]`) |
| `sample<number>` | exported | `[[]]` | array index out of bounds | violation: `src/array/sample.ts:17:10 arr[randomIndex]` | returned `undefined` (declared `number`) |
| `sentinelSearch` | exported | `[[-0, -Infinity, -97, -10], NaN]` | array index out of bounds | violation: `search/sentinel_search.ts:37:10 array[index]` | timeout (no result within 20 s) |
| `gatherScc` | internal | `[[], [], 0, [98, 492.5, 5.694854281447043e-181, -0]]` | array index out of bounds | violation: `graph/kosajaru.ts:43:7 visited[node]` | threw (TypeError: the value read is not iterable) |
| `getNodePriorities` | internal | `[[], [], [5, 82, 3.005866186518087e+201], 685597484]` | array write would create a hole | violation: `graph/kosajaru.ts:8:7 visited[node]` | threw (TypeError: the value read is not iterable) |

| unsound read tolerated (dyn) | API | input | Lean panic | Node, with checks | Node, checks off |
|---|---|---|---|---|---|
| `binarySearchIterative` | exported | `[[172, -160, 3664979655, -2137647482.784605], 755184333, ...` | array index out of bounds | violation: `search/binary_search.ts:26:16 array[start]` | returned `null` (declared `number | null`) |
| `binarySearchRecursive` | exported | `[[172, -160, 3664979655, -2137647482.784605], 755184333, ...` | array index out of bounds | violation: `search/binary_search.ts:52:16 array[start]` | returned `null` (declared `number | null`) |
| `fibonacciSearch` | exported | `[[], -398.5]` | array index out of bounds | violation: `search/fibonacci_search.ts:51:12 array[offset + 1]` | returned `null` (declared `number | null`) |
| `interpolationSearch` | exported | `[[], -398.5]` | array index out of bounds | violation: `search/interpolation_search.ts:18:30 array[lowIndex]` | returned `-1` (declared `number`) |
| `partition` | exported | `[[], 0, 98]` | array index out of bounds | violation: `sorts/quick_sort.ts:14:17 array[pivotIndex]` | returned `49` (declared `number`) |
| `CountSmallerItems` | internal | `[[], -398.5, 5]` | array read at a non-index key | violation: `sorts/cycle_sort.ts:50:23 array[i]` | returned `0` (declared `number`) |
| `dfs` | internal | `[[], [], 0, 5]` | array index out of bounds | violation: `graph/bipartite_graph.ts:7:7 colors[node]` | returned `false` (declared `boolean`) |
| `heapify` | internal | `[[], -398.5, 5]` | array read at a non-index key | violation: `sorts/heap_sort.ts:41:22 arr[left]` | returned `undefined` (declared `void`) |
| `swap` | internal | `[[], -398.5, 5]` | array read at a non-index key | violation: `sorts/heap_sort.ts:57:16 arr[i]` | returned `undefined` (declared `void`) |

| model limitation (dyn) | API | input | Lean panic | Node, with checks | Node, checks off |
|---|---|---|---|---|---|
| `isArray` | exported | `[({})]` | Array.isArray of an external object | returned: `false` | - |
| `isBoolean` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `isFunction (isFunction)` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `isFunction (isFunction_2)` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `isJSON` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `isNumber` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `isObject` | exported | `[({})]` | typeof of an external object | returned: `true` | - |
| `isObjectLike` | exported | `[({})]` | typeof of an external object | returned: `true` | - |
| `isString` | exported | `[({})]` | typeof of an external object | returned: `false` | - |
| `getPriority` | internal | `[({})]` | typeof of an external object | returned: `0` | - |

* Most latent bugs need arguments that the TypeScript types admit but the code does not expect:
  index arguments outside the array (`QuickSort`, `QuickSelect`), `NaN` (`pascalsTriangle`,
  `sentinelSearch`: the scan for `NaN` passes the sentinel and does not end), the empty array
  (`sample` returns `undefined` at type `T`). `gatherScc` and `getNodePriorities` are internal
  helpers (Kosaraju) that throw on a node outside the graph.
* Model limitation: `typeof` and `Array.isArray` of a host object (an `unknown` value the program
  did not create) have no result in the model (`StrictTS/Lib/Dyn.lean`), so the `unknown`
  predicates that use them panic on one.

**UNKNOWN, by first stuck construct** (`562bde2`, the `s[i]` functions and `trim` from `9e56ea6`;
the blockers, routed to the tactic owners):

| UNKNOWN, dyn: first stuck construct | functions | examples |
|---|---|---|
| while/for loop | 21 | `cb_chunkBy`, `cb_unionBy`, `cb_unionWith`, `cb_uniqWith` |
| for-of over an array | 21 | `escape`, `unescape`, `wrapAnsiBg`, `bgBlack` |
| builtin: arrFilter with a callback that captures variables | 7 | `cb_differenceWith`, `cb_intersectionWith`, `cb_isSubsetWith`, `difference<number>` |
| dyn operation result (Dyn.typeof, Dyn.eq, Dyn.isArrayTy, Dyn.truthy) not decided | 5 | `isNull`, `isUndefined`, `invariant`, `isNull` |
| external call answer | 5 | `streamToString`, `generateCombinations`, `generateAllCombos`, `BinarySearchTree<number>.inOrderTraversal` |
| other side condition | 4 | `Semaphore.acquire`, `trimEnd`, `trimStart`, `trim` |
| module variable cell (ModuleInit facts not derived) | 4 | `stringSize`, `createPadding`, `escapeString`, `uniqueId` |
| undecided test: index from an argument within bounds | 3 | `percentile`, `percentile`, `calculateMedian` |
| cell of a reference below the first level (World.Closed / Val.Live not used) | 3 | `Mutex.get isLocked`, `Mutex.acquire`, `BinarySearchTree<number>.insert` |
| external call answer (RegExp.test) | 3 | `parseHex`, `bgHex`, `hex` |
| for-of over a string | 3 | `Trie.insertNode`, `Trie.find`, `Trie.searchNode` |
| recursive call | 3 | `factorial`, `nthFibonacciRecursively`, `solve` |
| builtin: reduce without an initial value | 3 | `greatestCommonFactor`, `binaryLCM`, `lowestCommonMultiple` |
| undecided test on a value read at run time (dyn operation, string comparison) | 2 | `nullishRank`, `eq` |
| external call answer (ArrayBuffer.isView) | 2 | `isTypedArray`, `isTypedArray` |
| call not unfolded (second call, or after the unfolding phase) | 2 | `generateParentheses`, `binomialCoefficient` |
| for-of over a Map | 1 | `hasValue<number, number>` |
| heartbeat limit | 1 | `parseNestedBrackets` |

| UNKNOWN, strict: first stuck construct | functions | examples |
|---|---|---|
| for-of over an array | 21 | `escape`, `unescape`, `wrapAnsiBg`, `bgBlack` |
| while/for loop | 19 | `cb_unionBy`, `cb_unionWith`, `cb_uniqWith`, `cb_xorWith` |
| builtin: arrFilter with a callback that captures variables | 7 | `cb_differenceWith`, `cb_intersectionWith`, `cb_isSubsetWith`, `difference<number>` |
| module variable cell (ModuleInit facts not derived) | 4 | `stringSize`, `createPadding`, `escapeString`, `uniqueId` |
| external call answer | 4 | `BinarySearchTree<number>.inOrderTraversal`, `traverse`, `generateCombinations`, `generateAllCombos` |
| undecided test: index from an argument within bounds | 3 | `percentile`, `percentile`, `calculateMedian` |
| cell of a reference below the first level (World.Closed / Val.Live not used) | 3 | `Mutex.get isLocked`, `Mutex.acquire`, `BinarySearchTree<number>.insert` |
| external call answer (RegExp.test) | 3 | `parseHex`, `bgHex`, `hex` |
| for-of over a string | 3 | `Trie.insertNode`, `Trie.find`, `Trie.searchNode` |
| recursive call | 3 | `factorial`, `nthFibonacciRecursively`, `solve` |
| builtin: reduce without an initial value | 3 | `greatestCommonFactor`, `binaryLCM`, `lowestCommonMultiple` |
| call not unfolded (second call, or after the unfolding phase) | 2 | `generateParentheses`, `binomialCoefficient` |
| other side condition | 1 | `Semaphore.acquire` |
| heartbeat limit | 1 | `parseNestedBrackets` |

The largest groups: `while`/`for` loops that neither a summary nor the `JS.NoPanic` loop fallback
handles (sorts and searches that write or index the array; loops over a string: `deburr`,
`dedentImpl`, and `parseNestedBrackets` past the heartbeat limit; loops with a callback parameter's
wrapper); `for … of` over the match arrays of `String.matchAll` (the colour functions, `escape`,
`unescape`: the replacer loops of `replace`/`replaceAll`, which the extern specifications of
autosplit address); `filter` callbacks that capture variables or nest callbacks; results of
`unknown` operations (`Dyn.eq v null`, `Dyn.typeof v`) whose `none` case is impossible but not
refuted; answers of the `RegExp.test`/`ArrayBuffer.isView` externs and of host streams;
`ModuleInit` facts for es-toolkit's module (4); index arguments within bounds; `World.Closed`/
`Val.Live` (class N); the `Trie` walks over a word; recursion; `reduce` without an initial value.

## Problems found (reported, not fixed here)

* `ts_auto` / `ts_summarize`: (1) a loop or callback that follows an undecided test (an
  argument-validation `throw`, an early `return`) is not summarized: the residual goals of
  `findMin`, `median` and `max` show the test split only in the final step, with the loop (the
  `sort`) still unsummarized under it; this alone blocks the validating functions, under
  `JS.NoPanic` as well (splitting on the test before summarizing, then summarizing in each case,
  would address it); (2) counted loops bounded by a string length (the translator's
  own `split`) or by `xs.length - 1` (`isSortedArray`, `bubbleSort`), and backwards loops or loops
  starting at a computed index (`dropRightWhile`, `buildMaxHeap`); (3) callbacks whose closure
  captures a `Set`/`Map` (`difference`, `intersection`), callbacks nested in callbacks
  (`differenceWith`) or forwarded through a closure (`meanBy`); (4) `return`/`break` inside a
  loop over a Map or Set (`every`, `some`, `findKey`) or a counted loop (`takeWhile`,
  `linearSearch`); loops over Maps and Sets without one are summarized (`countBy`, `keyBy`,
  `mapValues` proved).
* Translator: `--emit-lean` leaves out generic functions, which are 41% (es-toolkit, 134/329)
  and 54% (TheAlgorithms, 89/166) of the covered functions with dyn; emitting one instance
  (`T := number`, as the wrappers here do) would make them objects of proofs. Coverage counts a
  function as covered even when a callee fails in the normal translation: in es-toolkit dyn, 49
  function bodies fail there and 76 more functions are left out because they call one.
* Statement generator (`attempts.py`): references below the first level (the inner arrays of a
  `number[][]`, objects held in fields) get no cell, so those statements are false in some worlds
  (class N); allocated inner cells as hypotheses would make them real attempts.
* Upstream: TheAlgorithms' `data_structures/set/map_set.ts` imports a module that does not exist
  at that path (TS2307).

## Reproduction

From the worktree root (every step is one guarded job: one core, under 10 minutes):

```sh
tools/run.sh 0.05 300 tools/public/fetch.sh                      # sources at the pinned commits
for p in es-toolkit thealgorithms-ts; do for m in strict dyn; do
  tools/run.sh 0.2 590 tools/public/coverage.sh $m $p            # report + emitted module
done; tools/run.sh 0.2 590 tools/public/mono_emit.sh dyn $p      # generic wrappers
tools/run.sh 0.2 590 tools/public/mono_emit.sh dyn $p cb; done    # fixed pure callbacks
for f in scratch/public/lean/Cov_*.lean; do tools/public/elab.sh $f; done
A=scratch/public/auto
python3 -I tools/public/attempts.py scratch/public/lean/Cov_es_toolkit_dyn.lean $A --per-file 6
python3 -I tools/public/attempts.py scratch/public/lean/Cov_thealgorithms_ts_dyn.lean $A --per-file 6
python3 -I tools/public/attempts.py scratch/public/lean/Cov_es_toolkit_mono_dyn.lean $A --per-file 6 --exclude $A/Cov_es_toolkit_dyn_auto.json
python3 -I tools/public/attempts.py scratch/public/lean/Cov_thealgorithms_ts_mono_dyn.lean $A --per-file 6 --exclude $A/Cov_thealgorithms_ts_dyn_auto.json
python3 -I tools/public/attempts.py scratch/public/lean/Cov_es_toolkit_cb_dyn.lean $A --per-file 6 --select-prefix cb_
# JS.NoPanic for the class-B (validating) functions, named from the first verdicts (results.py)
python3 -I tools/public/attempts.py scratch/public/lean/Cov_es_toolkit_dyn.lean $A --per-file 6 --statement NoPanic \
  --only percentile,trimEnd,trimStart,max,median_2,min,percentile_2
python3 -I tools/public/attempts.py scratch/public/lean/Cov_thealgorithms_ts_dyn.lean $A --per-file 6 --statement NoPanic \
  --only aliquotSum,calculateMean,DoubleFactorialIterative,findFactors,findMin,binaryGCF,hammingDistance,isSquareFree,isPrime,sieveOfEratosthenes,squareRoot
python3 -I tools/public/attempts.py scratch/public/lean/Cov_es_toolkit_cb_dyn.lean $A --per-file 6 --statement NoPanic --select-prefix cb_ \
  --only cb_maxBy_2,cb_medianBy_2,cb_minBy_2
for f in $A/*.lean; do tools/public/prove.sh $f; done
for m in Cov_es_toolkit_dyn Cov_es_toolkit_mono_dyn Cov_es_toolkit_cb_dyn Cov_thealgorithms_ts_dyn Cov_thealgorithms_ts_mono_dyn \
    Cov_es_toolkit_dyn_nopanic Cov_es_toolkit_cb_dyn_nopanic Cov_thealgorithms_ts_dyn_nopanic; do
  python3 -I tools/public/results.py $A $m; done
python3 -I tools/public/analyze.py scratch/public/out es-toolkit:2 thealgorithms-ts:1                 # coverage tables
python3 -I tools/public/proof_tables.py $A es-toolkit=Cov_es_toolkit_dyn "es-toolkit generic@number=Cov_es_toolkit_mono_dyn" \
  "es-toolkit with fixed pure callbacks=Cov_es_toolkit_cb_dyn" TheAlgorithms=Cov_thealgorithms_ts_dyn \
  "TheAlgorithms generic@number=Cov_thealgorithms_ts_mono_dyn"
node tools/public/generic_count.js scratch/projects/es-toolkit scratch/public/out/es-toolkit.dyn.json   # generic covered units
```

Uniform NoPanic, on a git-archive copy of a master commit C (`70f729b`; `2e3c32d` with the same
emitted modules and attempt files; `562bde2`, `2ea47b8` and `e57150b` with everything redone;
`9e56ea6` for the recheck; outputs in `scratch/nopanic`, `scratch/nopanic_2e3c32d`,
`scratch/nopanic_562bde2`, `scratch/nopanic_9e56ea6`, `scratch/nopanic_2ea47b8` and
`scratch/nopanic_e57150b`):

```sh
C=2e3c32d; mkdir -p scratch/base_$C && git archive $C | tar -x -C scratch/base_$C
ln -s "$(readlink -f frontend/node_modules)" scratch/base_$C/frontend/node_modules
(cd scratch/base_$C && ../../tools/run.sh 1.5 590 lake build)
ROOT=$PWD; export TREE=$ROOT/scratch/base_$C PUB=$ROOT/scratch/nopanic
for p in es-toolkit thealgorithms-ts; do for m in strict dyn; do
  tools/run.sh 0.2 590 tools/public/coverage.sh $m $p
  for k in mono cb; do tools/run.sh 0.2 590 tools/public/mono_emit.sh $m $p $k; done
done; done
for f in $PUB/lean/Cov_*.lean; do tools/public/elab.sh $f; done        # (empty TheAlgorithms cb modules skipped)
for m in NoPanicDiag PanicSearch; do (cd $TREE && $ROOT/tools/run.sh 0.1 300 lake env lean -DElab.async=false \
  -R $ROOT/tools/public/lean -o $PUB/diag/$m.olean -i $PUB/diag/$m.ilean $ROOT/tools/public/lean/$m.lean); done
for m in dyn strict; do                                                  # attempts: every function
  python3 -I tools/public/nopanic.py $PUB/lean/Cov_es_toolkit_$m.lean $PUB/np --set "es-toolkit $m"
  python3 -I tools/public/nopanic.py $PUB/lean/Cov_es_toolkit_mono_$m.lean $PUB/np --set "es-toolkit generic@number $m" \
    --exclude $PUB/np/Cov_es_toolkit_${m}_np.json
  python3 -I tools/public/nopanic.py $PUB/lean/Cov_es_toolkit_cb_$m.lean $PUB/np --set "es-toolkit fixed callbacks $m" \
    --only-prefix cb_ --exclude $PUB/np/Cov_es_toolkit_${m}_np.json --exclude $PUB/np/Cov_es_toolkit_mono_${m}_np.json
  python3 -I tools/public/nopanic.py $PUB/lean/Cov_thealgorithms_ts_$m.lean $PUB/np --set "TheAlgorithms $m"
  python3 -I tools/public/nopanic.py $PUB/lean/Cov_thealgorithms_ts_mono_$m.lean $PUB/np --set "TheAlgorithms generic@number $m" \
    --exclude $PUB/np/Cov_thealgorithms_ts_${m}_np.json
done
python3 -I tools/public/np_plan.py $PUB/np > $PUB/np_files.txt         # dyn + the strict ones not identical to a dyn one
cat $PUB/np_files.txt | xargs -P 3 -n 1 env TIMEOUT=300 CAP=0.1 tools/public/prove.sh
python3 -I tools/public/np_verdicts.py $PUB/np
python3 -I tools/public/np_search.py $PUB/np $PUB/search > $PUB/search_files.txt     # counterexample search
cat $PUB/search_files.txt | xargs -P 2 -n 1 env TIMEOUT=90 CAP=0.05 tools/public/prove.sh
#   second pass for the searches that did not finish (list their keys in KEYS): small numbers
python3 -I tools/public/np_search.py $PUB/np $PUB/search --runs 100 --keys KEYS --tag psm --small --seed 11
for b in "thealgorithms-ts:scratch/projects/thealgorithms-ts" "es-toolkit:scratch/projects/es-toolkit"; do
  tools/run.sh 0.2 400 node tools/public/node/build.js ${b#*:}/tsconfig.strictts.json $PUB/node/${b%%:*} ${b#*:}; done
tools/run.sh 0.2 400 node tools/public/node/build.js $PUB/mono/es-toolkit-cb-dyn/tsconfig.json $PUB/node/es-toolkit-cb scratch
python3 -I tools/public/np_node.py $PUB/np $PUB/search $PUB/node > $PUB/search/node.jsonl          # Node confirmation
python3 -I tools/public/np_report.py $PUB/np $PUB/search                                           # tables
#   the second commit: same lean/ and np/ files in another PUB, elaborated and run with its TREE;
#   attempts that reach Lean's default heartbeat limit (files written before `HEARTBEATS` was in
#   nopanic.py) run again with `set_option maxHeartbeats 1000000 in` in np_hb/, then
#   np_verdicts.py PUB2/np --override PUB2/np_hb
#   np_report.py PUB2/np $PUB/search --before $PUB/np 70f729b 2e3c32d                 # before/after
#   a commit with another translator: everything again in PUB3, then
#   np_report.py PUB3/np PUB3/search --compare PUB2/np $PUB/search 2e3c32d 562bde2     # matched by signature
python3 -I tools/public/np_search.py $PUB/np $PUB/search_proved --proved --tag pp                  # cross-check
#   host specifications (on 883a989 and 9e56ea6): the base modules again, attempts with and without
#   --ext-specs, run only the files whose theorem gained an `hext` hypothesis (and the same files without them)
python3 -I tools/public/nopanic.py $PUB/lean/Cov_es_toolkit_dyn.lean $PUB/np_ext --set "es-toolkit dyn" --ext-specs
#   recheck on 9e56ea6 (PUB4; modules emitted again, attempts in np_noext compared with PUB3's by
#   closure_hash): run the files whose code changed, search those not proved (KEYS), then
python3 -I tools/public/np_search.py PUB4/np_noext PUB4/search_six --keys KEYS --tag ps
python3 -I tools/public/np_report.py PUB3/np PUB3/search --compare PUB2/np $PUB/search 2e3c32d 562bde2 \
  --recheck PUB4/np_noext PUB4/search_six 9e56ea6 deburr,dedentImpl,trimEnd,trimStart,hammingDistance,parseNestedBrackets,trim
#   2ea47b8 (PUB5, everything again, at most 2 jobs at once): the base modules with
#   EMIT_FLAGS=--no-emit-generics tools/public/coverage.sh MODE NAME, the rest as above; the small
#   pass also for the cross-check (np_search.py --proved --runs 100 --keys KEYS --tag ppsm --small --seed 11), then
python3 -I tools/public/np_report.py PUB5/np PUB5/search --compare PUB3/np PUB3/search 562bde2/9e56ea6 2ea47b8 \
  --compare-recheck PUB4/np_noext PUB4/search_six 9e56ea6 deburr,dedentImpl,trimEnd,trimStart,hammingDistance,parseNestedBrackets,trim
#   e57150b (PUB6, everything again; the attempt files import StrictTS and end with np_used), then
python3 -I tools/public/np_report.py PUB6/np PUB6/search --compare PUB5/np PUB5/search 2ea47b8 e57150b
```

`tools/public/export.py` writes `tools/public/results/coverage_<project>.tsv` (one row per
function and mode: file, line, name, kind, LOC, status, rules) and `proofs.tsv` (one row per
attempt: function, signature, IR features, verdict, class; the uniform NoPanic rows are the
`e57150b` verdicts, with the counterexample input or the first stuck construct).
