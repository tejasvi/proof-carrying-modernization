# StrictTS — a Lean 4 semantics and proof kit for statically typed TypeScript

StrictTS is a sound, statically typed subset of TypeScript with:

* a **formal semantics in Lean 4**: an intrinsically typed IR and a definitional interpreter
  (one `partial_fixpoint` definition — no fuel, no type-error states);
* **native Lean models** of the runtime: exact IEEE-754 `number` (`F64`), fixed-width integers
  and typed arrays (`BitVec`), UTF-16 strings, `Array`, `Map`/`Set` (insertion order,
  SameValueZero), `Promise`/`async`/microtasks/timers;
* a **translator** from real TypeScript (TypeScript 5.9 compiler API) that checks the subset
  rules and emits Lean;
* **proof automation** for differential equivalence and invariants: symbolic execution
  (`ts_sym`), **invariant-free loop summarization** (`ts_summarize`, `ts_callbacks`: loops and
  array callbacks become folds of their computed effect), the one-call proof attempt `ts_auto`,
  invariant rules for the rest (`ts_forof`, `ts_while`, partial correctness), library models,
  a number bridge (safe integers ↦ `Int`, int32 idioms ↦ `BitVec 32`), async job-queue lemmas
  and `bv_decide`/`omega`/`grind`;
* **external libraries as oracles** (Firestore, loggers, `RegExp`, `JSON`): typed calls whose
  answers are hypotheses, so theorems hold for every library behaviour;
* **specs in TypeScript** (JSDoc `@requires`/`@ensures` → Lean propositions) and random
  differential testing (`diffCheck`, `specCheck`, and the `strictts-diff` tool).

## Results on real code (2026-10-24)

* **Coverage** of two production TypeScript code bases (another-project-app, a second project), reported
  separately for the strict subset and for its extension with checked dynamic values
  (`--strict` selects the former). On snapshots another-project@5932a72 + second-project@3574718 (7,198
  functions; 10-24):
  * strict subset (no `unknown`/`any`): 3,218 functions (44.7%);
  * with `unknown`/`any` as checked dynamic values (`Ty.dyn`: casts panic on mismatch):
    5,080 functions (70.6%).
  The 10-24 additions raised these from 41.7% / 64.0% on the same snapshots: function values and
  records compared by identity (listener sets `Set<() => void>`, Map keys, `===`) as boxed cells,
  index-signature types with named properties as dictionaries, regular expressions without `g`/`y`
  as values (also built with `String.raw`), `console.warn`/`error`, and a few library forms. On 10-23 the same
  configuration covered 2,876 (41.5%) and 4,393 (63.4%) of 6,926 functions; at the start of
  that day, 925 (13.4%). The translator emits the covered functions without an elaboration
  error; coverage-mode emission (`--coverage --emit-lean`) instantiates each covered generic
  function once (each type parameter := number, string for `extends PropertyKey` / `string`),
  so what is proved about it is about that instance (`--no-emit-generics` leaves them out).
* **Public code** (`tools/public`, pinned commits, reproducible with `tools/public/fetch.sh`),
  translator of master `2ea47b8`: es-toolkit v1.52.0: strict 277/794 functions (34.9%, 20.8% of
  the lines), with dynamic values 422/794 (53.1%, 32.6%); TheAlgorithms/TypeScript: strict
  165/234 (70.5%, 58.9%), with dynamic values 170/234 (72.6%, 60.6%) (on `5044b3c`, 10-23: 230,
  329, 163 and 166). All emitted modules elaborate. On `5044b3c`, a blanket "never throws or
  panics" statement attempted by `ts_auto` alone on every emitted loop function is false for 72
  of 95 of them (input validation by throwing, arbitrary callbacks, inner references, inputs such
  as NaN found by reading the code); over the attempts whose statement may be true, `ts_auto`
  proves 5/10 (es-toolkit) and 0/13 (TheAlgorithms: `while` loops and loops bounded by a number
  parameter). With a fixed pure callback, 26 of 47 es-toolkit callback functions are proved
  (among them real loops: countBy, keyBy, mapKeys, mapValues, filter/forEach/map over Maps
  and Sets, sumBy, uniqBy, medianBy). For the 21 functions that validate their arguments by
  throwing, `JS.NoPanic` is proved for 15: `ts_auto` splits on the validation before
  summarizing (max, min, maxBy, minBy, calculateMean, findMin), falls back to a
  partial-correctness rule for loops it cannot summarize (aliquotSum, DoubleFactorialIterative,
  binaryGCF, isPrime, isSquareFree, squareRoot, findFactors), and indexes sorted copies at
  rounded positions (median, medianBy); 0 before. See `tools/public/RESULTS.md`.
* **One statement for every public function** (`JS.NoPanic`: no run reaches a state where the
  TypeScript types are unsound, such as an out-of-bounds read typed `T`, or an uncovered
  construct; returning, throwing and diverging are allowed), proved by `ts_auto` alone with no
  annotation (master `e57150b`, attempts importing the root `StrictTS`): es-toolkit 144/191
  functions in the strict subset (75%), 174/245 with dynamic values (71%); TheAlgorithms 36/82
  (44%) and 36/83 (43%). For the others, a
  search through the executable semantics, confirmed in Node with checked reads, finds 7 latent
  bugs, where an input the types admit makes a value the types exclude escape
  (`sample<number>([])` returns `undefined` at type `number`, `pascalsTriangle(NaN)`,
  `sentinelSearch(xs, NaN)` does not terminate, `QuickSort`/`QuickSelect` with out-of-range
  indices, two Kosaraju helpers), 11 reads outside the types that the code happens to tolerate
  (among them es-toolkit's `reduce` over a Map or Set without an initial value, `initialValue!`),
  and 11 model limitations (`typeof` of host objects, a cast of a boolean to `ArrayLike`); the
  search finds no panic on any proved function. With two ECMA-262 facts about
  the host's regular-expression answers as hypotheses (`World.ExtSpec`: a `matchAll` array is
  fresh, a match result has an element 0; errors stay possible), 20 of the 23 functions that
  reach those externs are proved (the colour helpers of es-toolkit, `wrapAnsiBg`, TheAlgorithms'
  `XORCipher`), against 2 without (`tools/public/RESULTS.md`, "With host specifications").
* **Automatic proofs.** `ts_auto` proves, with no invariant and no argument, every loop/callback
  example of `examples/Summarize` (sum/max loops ≡ `reduce`, push loop ≡ `filter`, flag loop ≡
  `some`/`every`, loops with `break`/`continue`, counted `for` loops, string/`Map`/`Set` loops).
  On the 67-pair refactoring benchmark (`tests/equiv-bench`): 43/44 equivalences proved, 32 for
  every world, 5 for worlds with allocated argument cells, 2 also assuming string lengths below
  2^53 (the ECMAScript maximum), 1 also assuming object arguments allocated with their fields
  initialised and array fields shorter than 2^32 - 1 (room for one `push` below the JavaScript
  limit), and 3 under the weaker observational statement (equal results, console output and
  cells that existed before the call; cells the callee allocates, the allocation counter and
  async state are not compared; definitions from equiv-lean, `StrictTS/Proof/Obs.lean`) (loops vs
  `reduce`/`map`/`filter`/`some`/`every`/`find`/`findIndex`/`includes`/`join`, `while` vs
  `for`, loop fusion, recursion vs loop, inlining, `switch` vs if-chains, a class method, a `Map`
  table vs an if-chain, `slice` vs `concat([])`, early returns, guard clauses, int32 idioms,
  async, …), 23/23 non-equivalences refuted with a concrete input, no wrong verdict. Left: 34
  (a loop that writes two cells).
* **Library histories** (`tools/difftool/r6*/`; each run's inputs were frozen by the paper's
  evidence owner before it ran, and each run was checked after): every commit's changed
  self-contained functions, old against new, with no annotation. es-toolkit (v1.0.0..v1.52.0, 415
  pairs): 70 equivalences proved (R6e, master `4016a4a`; first run R6: 46), 86 behaviour changes
  refuted by a Node counterexample (10 also confirmed in Lean), 76 of them calls the public
  TypeScript signatures admit; in commits whose message promises unchanged behaviour
  (refactor/perf/style/chore), 16 equivalences are proved and four refutations changed what a
  typed caller sees: `uniq([-0])`, `toPath("..")`, `toPath("]")` and the internal
  `areObjectsEqual`. remeda (862 pairs): 61 proved (R6e; first run R6r: 54), 64 refuted, none of
  them in such a commit a change a typed caller of the library can see. The difftool compares at
  one instance of a generic function, on the old version's parameter types when the new version
  widens them (`__difftool_compat`), and at the other version's declared return type when it
  changes (`__difftool_ret`). A weaker statement, `old-no-panic` (equal runs, or the old run
  panics), holds for 1 further es-toolkit pair and 2 remeda pairs (a return type widened from `T`
  to `T | undefined`); it is reported separately, never as an equivalence. equiv-lean proves two
  more es-toolkit perf commits relationally, modulo a fresh `Set` (`difference`, `intersection`).
* **Real functions** (copied from the private another-project-app code base; kept in `examples/Real`
  locally and not tracked):
  * `takeWithinBudget` (a greedy token-budget loop): a refactoring that tests `used + cost <=
    budget` instead of `!(used + cost > budget)` is refuted (it differs for a NaN budget; Node
    agrees), and the correct refactoring is **proved** equivalent for every array, budget and
    world, and every pure cost function (the callee is used through its contract);
  * `estimateTokens` (a loop over a string's code points): its closed form is proved;
  * `deleteCover`, `ownerUidOf`, `bumpReports` (async functions calling Firestore/Storage and a
    logger): what they write and when, and that they never fault, for every library answer
    (each a single `ts_auto` call); `bumpReports`'s "never throws" comment is proved.
* **Validation**: the Lean semantics prints what Node prints on the whole corpus (187 entries:
  144 programs, 41 rejection tests, 2 coverage-mode tests), and
  0 mismatches over about 2,900 random inputs to 172 translated functions. Every public function
  that the translator emits and a driver can call (276 of es-toolkit and TheAlgorithms) was run
  on the same inputs under Node and under the Lean interpreter (`tools/validate`): of 11,372
  inputs, 11,170 agree on the result, normal or exceptional exit, console output and final
  arguments; the others are designed panics (reads that the types exclude, all of which fail at
  the same read in a Node build that checks every such read: 384 of 384 after rerunning the
  inputs behind them) and one model limitation (`===` on records inside `unknown`). The run
  found and fixed five bugs, among them `Number.isInteger`/`isFinite`/… evaluating to `false` on
  values not statically typed `number`.

The design goal is the least proof effort per line of real code: no proof ever branches on
dynamic types, implicit coercions or prototypes, because the subset excludes them and the IR
cannot express them. See [DESIGN.md](DESIGN.md) for the rationale and the subset rules.

## Example: proving a refactoring

[`examples/Refactor/sum.ts`](examples/Refactor/sum.ts):

```ts
export function sumLoop(xs: number[]): number {
  let s = 0;
  for (const x of xs) { s = s + x; }
  return s;
}
export function sumReduce(xs: number[]): number {
  return xs.reduce((acc, x) => acc + x, 0);
}
```

```sh
node frontend/dist/cli.js --namespace SumEx -o examples/Refactor/SumEx.lean examples/Refactor/sum.ts
```

[`examples/Refactor/SumProof.lean`](examples/Refactor/SumProof.lean) proves, for every input
array and every world (heap, console, job queue):

```lean
theorem sumLoop_eq_sumReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program sumLoopRef (.cons (.arr a) .nil)) w =
      exec (callFun I program sumReduceRef (.cons (.arr a) .nil)) w
```

The loop half is ten lines; the only creative input is the invariant:

```lean
  rw [sumLoop_call]
  simp only [sumLoopDef, ts_sym]
  ts_forof xs using
    (fun i env w₁ => env = .cons (.num (sumSpec (xs.toList.take i))) (.cons (.arr a) .nil) ∧ w₁ = w)
  case cell => rintro i env w₁ ⟨-, rfl⟩; exact hw
  case step => rintro i env w₁ hi ⟨rfl, rfl⟩; simp [ts_sym, sumSpec, List.take_add_one, List.foldl_append, hi]
  case init => exact ⟨by simp [sumSpec], rfl⟩
  ...
```

No assumption that the numbers are integers or finite is needed: both functions denote the
same IEEE left fold, NaN and `-0` included.

The invariant is not needed either. `ts_summarize` executes the loop body once on a symbolic
state, reads its effect off as a step function and rewrites the loop to a left fold of it;
`ts_callbacks` does the same for the `reduce` callback. The whole equivalence proof
(`sumLoop_eq_sumReduce_auto`) is then the same five lines for any such pair of functions:

```lean
  rw [sumLoop_call, sumReduce_call]
  simp only [sumLoopDef, sumReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]
```

### More worked examples (all on translator output, standard axioms unless noted)

| Example | TypeScript | What is proved |
|---|---|---|
| [`examples/Refactor`](examples/Refactor) | `for…of` sum vs `reduce` | equality of the two functions on every array and world |
| [`examples/Hash`](examples/Hash) | FNV-1a over a string: shifts and additions vs `Math.imul` | both compute the 32-bit FNV-1a fold of the UTF-16 code units; hence equal (the 32-bit identity is proved by `bv_decide` and by the kernel alone with `bv_omega`; the theorem uses the kernel-only proof) |
| [`examples/Invariant`](examples/Invariant) | `class Account` with `deposit`/`withdraw` that throw on bad input | the constructor establishes `balance ≥ 0`, every method preserves it on every path, including the throwing ones |
| [`examples/Maps`](examples/Maps) | word counting with `Map<string, number>` | the result maps each string to its number of occurrences; `CountAuto.lean`: with no invariant, the function's whole effect is a fresh `Map` holding a fold over the words |
| [`examples/Summarize`](examples/Summarize) | loops with `if`, `continue`, two accumulators, string building; `reduce` with a ternary | invariant-free: `maxOf` (loop) equals `maxOfReduce` on every array and world; the meaning of a loop with `continue`, computed; "never throws or panics" for the others |
| [`examples/Summarize/validating.ts`](examples/Summarize/validating.ts) | functions that validate their arguments before a loop (`if (xs.length === 0) throw …`, `if (factor < 0) throw …`, a `some` callback as the test, an early `return`) | by `ts_auto` alone (`TsAutoValidating.lean`): `JS.NoPanic` for every array and argument; `JS.Returns` and exact results under a precondition that rules the validation out (`xs.size ≠ 0`, `k.lt 0 = false`, `t ≠ .nan`); a caller that catches the exception returns for every array |
| [`examples/Extern`](examples/Extern) | synchronous library calls the semantics does not model: `/^[a-z]+$/.test(s)`, `s.normalize("NFC")`, `s.split(/\s+/)`, a regex validation that throws, a regex test before a loop | by `ts_auto` (`LibProofs.lean`): `JS.NoPanic` for every oracle; `JS.Returns` when the library does not throw (`w.ExtReturns f`); the exact result from the oracle's answer (`isLowerWord` returns the answer, `checkedName` the trimmed name when the regex says "not blank") |
| [`examples/Partial/numloops.ts`](examples/Partial/numloops.ts) | number-theory loops with no termination argument: `for (let d = 2; d * d <= n; d++)` with `return` inside, a bound `n / 2`, Euclid's `while`, a step `k -= 2`, `while (true)` left by `return`, a loop filling a `Set`, a counter indexing two strings (`hamming`) | by `ts_auto` alone (`NumLoopsAuto.lean`): `JS.NoPanic` / `JS.NoFault` for every argument (strings: fewer than `2 ^ 53` code units), through `evalLoop_cases_exit` (no iteration panics or changes the world, from any state with the loop's `const` values and the inferred slot candidates: kept values, a counter that stays a safe natural) |
| [`examples/ModuleVars`](examples/ModuleVars) | functions that read module-level constants (`const LIMIT = 3`, a string, a `Set`, an array), in a ternary, a loop and a validation | by `ts_auto` under `w.ModuleInit I program` (`ModVarsProofs.lean`): `JS.Returns`, `JS.NoPanic` and an exact result; without the hypothesis the statement fails (an uninitialised box throws a `ReferenceError`) |
| [`examples/Async`](examples/Async) | `async function double(n)` with an `await` | its promise is fulfilled with `2n` after the microtask queue runs |
| [`examples/Partial`](examples/Partial) | the Collatz loop `while (n !== 1) { n = n % 2 === 0 ? n / 2 : 3 * n + 1; steps = steps + 1; }`, whose termination is an open problem | no termination argument: every run that returns, for any `number` (NaN, ±∞, fractions included), returns a natural number and changes nothing; `collatz` never throws or panics |
| [`examples/Async/race.ts`](examples/Async/race.ts) | a lost update: `await Promise.all([inc(c), inc(c)])` where `inc` reads `c.n`, awaits, then writes the value read plus one | the counter ends at `x + 1` (`1` for a new counter): the lost update is deterministic under the job semantics; reading after the `await` gives `x + 1 + 1` (`2`); the whole program prints `racy: 1`, `fixed: 2`, as Node does (`race_output`); each of these proofs is one `ts_drain` call; the two resumptions commute (`exec_drain_swap`), so either order gives the same outcome; for any number `k` of queued resumptions, `incFixed` adds `k` and `incRacy` leaves the value read plus one (`exec_drain_specs`), in every order (`exec_drain_perm`) |
| [`examples/Async/rename.ts`](examples/Async/rename.ts) | `await getDoc(db, id)`, then `await setName(db, id, name)` unless the document is missing: two calls of an external database library (`Db`, `Doc` external types) | for every oracle answering the calls: a missing document fulfils the promise with `false` after one call (`setName` is never called); otherwise the second call is `setName(db, id, name)` and the promise is fulfilled with `true` or rejected with its error; the call and its queue never panic or throw (`NoFault`) |
| [`examples/Async/OutputProof.lean`](examples/Async/OutputProof.lean) | whole programs of the corpus: timers with nested timers and microtasks (`timers.ts`), three async workers that interleave at the `await`s in their loops (`interleave.ts`), `Promise.all`/`Promise.race` ordering (`all_race.ts`) | the console output of the whole run is Node's, for every implementation of the host functions (one `ts_drain` call each) |
| [`examples/Async/AllTupProof.lean`](examples/Async/AllTupProof.lean) | `Promise.all` over a tuple of different types and `Promise.allSettled` over a tuple with a rejection, against a then chain (`all_tuple.ts`) | the console output of the whole run is Node's (the simp call of `ts_drain`, with `decide` for the compared string literals) |
| [`examples/Specs`](examples/Specs) | JSDoc contracts: `@ensures result !== xs` and `@ensures result.length === xs.length` on a `map`; `@requires lo <= hi` / `@ensures lo <= result && result <= hi` on `clamp` | the two `map` contracts are proved; `specCheck` finds that `clamp`'s fails on NaN; once `@requires` adds `x === x` (`clampChecked`) the contract is proved |
| [`examples/Testing`](examples/Testing) | `indexOf(x) !== -1` vs `includes(x)`; `x < 0 ? -x : x` vs `Math.abs` | `diffCheck` finds the counterexamples (`NaN`; `-0`) in milliseconds |
| [`examples/Concrete`](examples/Concrete) | unit tests in the style of es-toolkit's: `median` (a `sort((a, b) => a - b)` over literals), `lerp` with `0.5`/`0.25`, `%` and `.length` in a loop, a `while` loop computing `10^20`, `round` (`Math.round`, `Math.pow(10, 0)`) | each test function returns normally (every expectation holds) for every implementation `I`, by `ts_eval` alone; `round(1.2345, 2)` under `I.pow 10 2 = 100` (`10 ** 2` is implementation-approximated) |
| [`tests/proof/HashEquiv.lean`](tests/proof/HashEquiv.lean) | one FNV step, shifts vs `Math.imul` (hand-written IR) | equal for all `number` inputs (NaN, ±∞, fractions): `ts_sym` then `ts_int32` |

## Proof toolkit

| Tactic / lemma | Use |
|---|---|
| `rw [f_call]` | unfold one call of a translated function (the translator emits `f_call` for each function) |
| `ts_sym [defs…]` / `simp [ts_sym, …]` | symbolic execution of IR on a symbolic world: reads become heap lookups, writes inserts |
| `ts_forof xs using Inv` | apply the index-based invariant rule to a `for (const x of arr)` loop found in the goal; goals `cell`, `step`, `init` |
| `ts_while Inv, V, Post` | invariant + variant rule for `while` and counted `for` loops; goals `step`, `init` |
| `ts_while_partial Inv, Post` | invariant-only rule for `while` and counted `for` loops that may run forever (partial correctness); goals `step`, `init` |
| `evalLoop_partial`, `evalDo_partial`, `evalForOf_partial`, `evalLoop_noFault`, `JS.NoFault.bind` | every run of a `while`/`for`, `do … while` or `for … of` (over an array the body may grow) that ends satisfies the exit condition; a loop (and code around it) whose iterations never fault never faults |
| `ts_summarize [lemmas]` | rewrite the first `for (const x of arr)` loop in the goal to `List.foldl` of the body's effect, computed by symbolic execution: the fold's state is the tuple of the mutable variables and, if the body writes one heap cell (`push`, `Map.set`, a field), that cell's content; `if`/`continue` are merged into `if`s in the step function; no invariant. A counted loop `for (let i = k0; i < n; i++)` (`n` an array length or a constant) becomes the fold over the positions `(List.finRange n).drop k0`, or over the elements when the body reads the array only at the counter. `ts_summarize [lemmas]` adds lemmas (e.g. a callee's contract) to the symbolic execution of the body |
| `ts_callbacks [lemmas]` | rewrite the first array method with an effect-free callback (`reduce`, `map`, `filter`, `some`, `every`, `find`, `findIndex`, `findLast`, `findLastIndex`, `forEach`, `sort`) to the standard function (`List.foldl`, `Array.map`, `Array.filter`, `Array.any`, …) of the callback's computed meaning; `lemmas` (e.g. a callee's contract) are added to the symbolic execution of the callback |
| `ts_merge [lemmas]` | close `lhs = rhs` where `rhs` has metavariables to be read off: evaluate `lhs`, split on stuck conditions and optional values inside one goal, merge the paths by anti-unification, assign by `rfl` |
| `JS.NoFault`, `JS.NoPanic`, `JS.Returns`, `Val.Live`, `World.Closed`, `callFun_of_lookup` | canonical "no panic, no uncaught exception" statements, liveness preconditions (`StrictTS/Proof/Contract.lean`), the call rule over an abstract program (`StrictTS/Proof/CallRule.lean`) |
| `--modular OUTDIR`, `f_call_of`, `f_lookup` | translator output with one Lean module per function and stable indices, for incremental proofs: a proof over an abstract program imports only the `Defs` modules of the functions it is about (`f_call_of` takes the lookup `P.funs[fRef.idx]? = some fDef` as hypothesis), so it is not rebuilt when other functions change; `f_lookup` instantiates it for `program` ([frontend/README.md](frontend/README.md#modular-output-incremental-cacheable-proofs), [`examples/Modular`](examples/Modular)) |
| `ts_int32` | int32 idioms on `number` (`\| 0`, `>>> 0`, `^ & \| ~ << >> >>>`, `Math.imul`, `+`/`-`) to `BitVec 32`, then `bv_decide` |
| `ts_safe` | discharge `F64.Safe n` (exact-integer) side conditions by `bv_omega` |
| `arrReduce_pure'`, `arrMap_pure'`, `arrFilter_pure'`, `arrSome_pure'`, … | `reduce`/`map`/`filter`/`some`/`every`/`find`/`findIndex`/`findLast`/`findLastIndex`/`forEach`/`sort` with an effect-free callback are `List.foldl`/`Array.map`/`Array.filter`/`Array.any`/`Array.all`/`Array.find?`/`Array.findIdx?`/(the same on the reversed array)/no effect/`sortBy`; `ts_callbacks` applies them |
| `JSMap.get?_set`, `get?_delete` | `Map` lookups after updates (for any key equivalence, SameValueZero included) |
| `F64.add_ofInt`, `lt_ofNat`, `ofNat_add_one`, `toInt32_ofInt`, … | the number bridge: safe integers compute exactly; int32 views are `BitVec 32` |
| `F64.round_ne_nan`, `ofNat_ne_nan`, `numEq_self_iff`, `le_of_not_lt`, `le_trans`, `ne_nan_of_le`, … | NaN and order (`F64Order`): rounding never produces NaN, so `x === x` on `ofNat n`/`ofInt n` is `true` by `simp` (`result.length === xs.length`); on non-NaN doubles `<`/`<=` form a total order (`¬(x < y)` gives `y <= x`), and `x <= y` holding makes both sides non-NaN |
| closed-number evaluation (`F64Eval`, in `simp` and `ts_sym`) | closed `number` terms on literals (`F64.ofNat 1 - F64.ofNat 2`, `0.5 * 100`, `Conv.isPos …`, `Math.floor/round/…`, comparisons, `%`, bitwise operators, index and length conversions, `String(x)`, the specified cases of `**`) are computed with the compiled `F64` definitions and replaced by their canonical literal (`F64.ofNat n`, `F64.ofInt (-n)`, `F64.mkFin neg man exp`, `F64.zero true`, `F64.nan`, `F64.inf b`); the kernel checks each step by evaluation (a few ms), no `decide` |
| `ts_eval [lemmas]` | prove a statement about a concrete run (a test case, a function on literals) by executing it: unfold the contract, compute the initialised module world, run with `ts_sym`, every function's call lemma, closed-number evaluation and `sortBy` on explicit lists, unroll loops one iteration at a time, use `ts_callbacks` for stuck array callbacks; `lemmas` join every step (e.g. `I.pow 10 2 = 100`) |
| `exec_drain_cons`, `exec_drain_nil` | run the microtask queue one job at a time |
| `ts_drain [defs…]` | symbolic execution of async code together with its microtask queue and event loop: each queued job runs under `ts_sym` until the queue is empty, then the earliest timer (array literals and `Promise.all` included); with `runOutput_eq` it computes the console output of a whole run |
| `ExtFun`, `World.answer`, `exec_extern`, `exec_externAsync` | external calls: declare a library function's signature (`abbrev getDoc : ExtFun := ⟨"pkg:getDoc", […], …⟩`), state the oracle's answers by call number (`hn : w.extIdx = n`, `w.answer getDoc vs n = .ok (.val v)`, then `n + 1`, …; an array result is answered with its elements, `.ok (.arr …)`, and allocated at the next address) and run the code with `ts_drain [hn, …]` or `ts_auto [hn, …]`; `ts_auto` splits on answers that no hypothesis fixes, in synchronous code too (an error, or a value of each form; a symbolic fresh array is allocated by `exec_materializeList_ok`); the optional hypothesis `w.ExtReturns f` (the library function `f` never answers with an error: a regex test, a string method) removes the error case, so that `JS.Returns` can hold ([`examples/Extern`](examples/Extern)) |
| `execAB_of_noAwait`, `runJob_await_of_noAwait`, `exec_drain_run` | atomicity: an `await`-free part of an async body is one big-step evaluation (`evalB`); the loop runs each job to completion before the next |
| `JobSpec`, `exec_drain_spec`, `exec_drain_specs` | a job's effect on the world without its queue, plus the jobs it appends (it never reads or reorders pending jobs); one loop step from a specification; a batch of jobs that enqueue nothing is the composition of their effects (`PreChain`: each finds its precondition) |
| `exec_drain_swap`, `exec_drain_perm`, `heap_insert_comm`, `heap_insert_of_get` | adjacent jobs with commuting effects can be swapped; a batch of pairwise independent jobs gives the same outcome in every order; writes to different cells commute; writing back a cell's value changes nothing |
| `World.ModuleInit I P w`, `moduleInit`, `runProgram_eq_moduleInit` | statements about functions that read module-level variables: the module's initialisation (allocate the module variables, run the module body) ends normally from the initial world and `w` still holds every cell it created (the world of a call after start-up, as `Testing.initWorld` builds for random tests); `ts_auto` runs the module body symbolically and turns the hypothesis into one heap fact per cell ([`examples/ModuleVars`](examples/ModuleVars)); a whole run is the initialisation followed by the event loop in the world it leaves |
| `StrictTS.Testing.diffCheck I P f g n` | random differential testing of two functions before proving |
| `node tools/jsdoc_specs.js IN.ts OUTDIR NS` | specs written in TypeScript: each `@requires`/`@ensures` becomes a function in a copy of the program (translated and evaluated by the same semantics), and `f_spec : Prop` states the contract (live arguments, fresh allocation pointer; no panic, no uncaught exception; partial correctness) |
| `StrictTS.Testing.specCheck I P f req ens n` | random testing of a contract: finds inputs that satisfy `req` but break `ens` (e.g. `clamp(NaN, lo, hi)`) |

### Partial correctness

`ts_while` needs a variant: it proves that the loop ends. For loops whose termination is
unknown, `ts_while_partial Inv, Post` applies `evalLoop_partial`: if every iteration from an
`Inv` state either diverges or runs the condition, body and step normally into an `Inv` state
(the step obligation of `ts_while` without the decrease, in weakest-precondition form), every
run that ends does so normally in a state satisfying `Post`. In the goal, the loop's run is
replaced by its normal exit (with `hpost : Post env' w'`); the case where it runs forever is
closed by `simp` when the goal is a partial-correctness statement
(`∀ r w', exec m w = some (r, w') → …`, e.g. an unfolded `JS.NoFault m w`), and otherwise left
as goal `diverge`. The rule is
proved by fixpoint induction on the interpreter's `partial_fixpoint` itself (`interp_induct`):
the approximations of `evalE` and `evalB` that one unfolding of the loop runs lie below the
real functions, so each of them either diverges or returns what the real function returns, and
the other functions of the mutual block need no motives of their own. `evalDo_partial` and
`evalForOf_partial` are proved the same way; rules for the other loop forms (the async loops,
`for … of` over a `Map`) reuse `interp_induct` (see `StrictTS/Proof/Partial.lean`).

`evalLoop_partial_exit` (`StrictTS/Proof/LoopExit.lean`) also lets an iteration leave the loop
(`return`, `throw`, `break`, a condition that throws) into states satisfying an exit condition;
only a panic is excluded. `ts_auto` uses it without any invariant for `JS.NoPanic` and
`JS.NoFault` goals with a `while` or counted `for` loop that no summary handles (a bound such as
`d * d <= n`, a step `k -= 2`, `while (true)` left by `return`): if no iteration panics or
changes the world from an arbitrary environment (checked by symbolic execution, with case splits
on the tests), the loop diverges or ends in the same world with `return v`, the normal exit
(not after `while (true)`) or, if an iteration may throw, an exception, and the code after the
loop is evaluated for each (`examples/Partial/NumLoopsAuto.lean`).

### Loop summarization

`ts_summarize` turns a `for … of` loop into a fold without an invariant. It encodes the
environment by the values of the mutable variables in scope (a tuple `σ`; `const` variables
never change), creates one metavariable per mutable variable for its value after an
iteration, and proves `exec body (x, s) = some (.ok (C x s, s'), w)` by symbolic execution
(`ts_merge`). When a `match` is stuck on a symbolic condition or optional value (`x > m`,
`m.get(k) ?? 0`), the goal is split inside one goal, both paths are evaluated, and their
results are anti-unified into one value with `if`s (or `Merge.optCase`) at the differing
positions, so `rfl` can assign the metavariables. If the body writes a heap cell, the cell
is detected from the symbolic result and its content joins the fold's state
(`evalForOf_summary_cells`). The kernel checks every step; a wrong guess only makes the tactic
fail. With `break` or `return`, the fold carries a flag or the returned value and stops changing
the state once it is set (`brkStep`, `retStep`); after a loop with `return`, the code that
follows runs for both completions inside one goal and the results are merged into `r.elim …`,
and the first-match lemmas (`findSome?_ite_const`, …, `Array.findIdx?_eq_finRange`) turn such
search loops into `any`, `all`, `find?` and `findIdx?` (`examples/Summarize/TsAutoReturns.lean`,
bench pairs 06-09). Loops over strings, `Map`s and `Set`s are folds over their code points or
live entries, with `continue`, `break` and `return` (`examples/Summarize/TsAutoLiveExits.lean`).
Counted loops are folds over the positions, with `continue`, `break` and `return` (the fold then
also keeps the position where the loop stopped, since the counter stays there). Forward loops
`for (let i = k0; i < n; i++)` (`evalLoop_count_pure`/`_cells`): the condition must evaluate to
`i < n`, `i < a - c` (`xs.length - 1`), `i <= e` or `i <= a - c` with the bound fixed and at
most `2^53` (an array length the body does not change, or a constant), rewritten to `i < n'`
(`lt_ofNat_sub_ofNat_eq`, …); the start may lie above the bound (the counter then ends at
`max k0 n`); positions are elements of `Fin n`, so the body can read `xs[i]` and `xs[i + 1]`
(`examples/Summarize/CountedLoops.lean`). Backwards loops `for (let i = xs.length - 1; i >= c;
i--)` or `i > c`, or from a literal start (`evalLoop_down_cells`): the counter before the test
at time `k` is the double `k - 1`, so the exit at `-1` needs no special case; a returning
iteration may allocate (`return xs.slice(0, i + 1)`: the fold keeps the world after it,
`evalLoop_down_cells_retw`). A backwards loop from the computed start `Math.min(Math.floor(n), m)`
with the test `i > c` is split on that test at the start (`evalLoop_split_start`): where it
holds, the start is `ofNat (min x.natVal m)` (`F64.floor_min_eq_ofNat_min`; NaN, `-Infinity`
and `-0` fail the test, `+Infinity` gives `m`); where it does not, the loop runs no iteration,
nor does any loop of the goal that the same test stops (the other side of an equivalence), and
`simp` closes that case on the spot (bench pair 03). The string concatenations in the step of a
backwards loop are right-associated (`JSStr.append_assoc`), so `out + String(i) + " "` and
`` out += `${i} ` `` give the same step. A `while` loop whose body ends with the counter step (`while (i <
n) { …; i++ }`, `while (i >= c) { …; i-- }`, no `break`/`return`) is the same fold
(`evalLoop_while_up_cells`, `evalLoop_down_while_cells`). Not yet covered: other `while` loops
(a counter that is not stepped last, or by another amount), counted loops with another step
(`i += 2`) or bound (`i * i <= n`, `i < Math.sqrt(n)`), other computed starts (forward loops
from a variable, `i >= c` from `Math.min(Math.floor(n), m)`, where `-0` passes the test), a loop
with both `break` and `return`, bodies that write two cells (an
experimental summary for a pair of cells is in the code but off), and continuing iterations
that allocate.
Loops and array callbacks may nest. When the symbolic execution of a body (`ts_merge`) reaches a
loop or an array method with a callback, it summarizes that one first, on the symbolic state of
the enclosing iteration (`ts_summarize`/`ts_callbacks` called from inside), so the outer step
function contains the inner fold: nested `for … of` and counted loops, `result.every(…)` over the
array a loop builds (`uniqWith`), `xs.filter(x => ys.every(…))` (`differenceWith`). A mutable
variable that a loop never assigns keeps its value instead of joining the fold's state (the
outer counter, read by the inner loop). Calls of non-recursive program functions in a loop body
or a callback are unfolded, also when the callee has a loop of its own. A callback that reads
the heap (another array, a `Set`) is not pure in every world, but it is in the world where the
method calls it, which is enough (`arrFilter_pureAt`, …, `StrictTS/Proof/CallbacksAt.lean`). A
counted loop that updates in place the array whose length it reads (`arr[i] = …`, swaps) has a
cell state of fixed size (`evalLoop_count_sized`: `{c // c.size = m0}`, the bound is `m0`)
(`examples/Summarize/TsAutoNested.lean`). Nested loops whose inner state needs an invariant
(selection sort's minimum index) stay open, and nested in-place updates (bubble sort) are
summarized but slow.
A test that the hypotheses decide is not split: `omega` decides a bounds test such as
`↑i < ys.size` for the counter `i : Fin xs.size` when a hypothesis says `xs.size ≤ ys.size`, and
the summary takes that branch, so loops over two arrays read off a step function
(`examples/Summarize/TsAutoZip.lean`: a dot product and a count of differing positions). Loops
whose state is used bitwise (hashes, CRCs) take the simp set `ts_bits`
(`StrictTS/Proof/Bits.lean`), which rewrites the bitwise operators on any operand into 32-bit
operations on `toInt32`, so that a masked table index such as `table[(h ^ xs[i]) & 0xFF]` is
decided inside the step (`examples/Summarize/TsAutoBits.lean`); it is opt-in because it changes
the normal form of every bitwise expression.
Simp lemmas identify the folds of push loops and flag loops with `filter`, `some` and `every`
(`foldl_push_filter`, `foldl_flag_true`, `foldl_flag_false_neg`, …), so such a loop and the
array method are proved equal by the same five lines (`examples/Summarize/AutoProofs.lean`).
A loop behind an undecided test (argument validation such as `if (xs.length === 0) throw …`, an
early `return`) sits in the continuation of the `match` on the `if` statement's outcome, where
no summary reaches it; `ts_auto` splits on the innermost undecided test of the goal (an `if`, an
optional value or a Boolean that is not a constructor), evaluates each case with its hypothesis,
closes the cases that contradict the statement's hypotheses (`omega` on length facts, via
`numEq_ofNat`/`lt_ofNat`; a precondition that gives the test the other value, compared up to
unfolding), and summarizes the loop in the remaining cases
(`examples/Summarize/TsAutoValidating.lean`).

### Equivalence when allocation differs

`exec (f args) w = exec (g args) w` is equality of the whole final world, including the
allocation counter. Refactorings that allocate a different number of objects (e.g.
`xs.filter(p).map(f)` versus one loop that pushes into a fresh array) are proved
equivalent through a common specification instead: prove that each function returns a fresh
array whose contents are `spec xs` and leaves every pre-existing cell unchanged, as
`countWords_spec` does for its `Map`.

## Layout

| Path | Contents |
|---|---|
| `StrictTS/Core/Ty.lean` | types, contexts, typed de Bruijn variables, type table |
| `StrictTS/Core/Syntax.lean` | the IR: expressions, statements, blocks, function literals, primitive operations, builtins |
| `StrictTS/Core/Val.lean` | runtime values (one constructor per primitive type), environments |
| `StrictTS/Core/World.lean` | completion records, async continuations, heap cells, `World`, the monad `JS` |
| `StrictTS/Core/Sem.lean` | the interpreter (`evalE`, `evalS`, loops, calls, builtins, async CPS), jobs, event loop, `runProgram` |
| `StrictTS/Num/F64.lean`, `F64Lemmas.lean` | exact binary64 model and the number bridge |
| `StrictTS/Num/Format.lean`, `Parse.lean` | `Number::toString`, `toFixed`/`toPrecision`/`toExponential`, `Number(s)`, `parseInt`/`parseFloat`, BigInt ↔ string |
| `StrictTS/Str/JSStr.lean`, `Lemmas.lean` | UTF-16 strings and their methods |
| `StrictTS/Lib/` | primitive semantics (`Prim.lean`), BigInt, conversions, `Map`/`Set` model |
| `StrictTS/Proof/` | `Exec` (symbolic execution), `Unfold`/`EqnsS` (the `ts_sym` set), `Loops`, `Partial` (invariant-only loop rules), `Arrays`, `Maps`, `F64Order` (NaN and the order of doubles), `Async`/`AsyncRace` (the job queue: atomicity, commutation, `ts_drain`), `Extern` (external calls), `Module` (statements over the initialised module world), `LoopExit` (loops left early, in partial correctness), `Tactics`, `Summarize` (loop summarization, path merging), `Auto` (`ts_auto`), `Contract` (no-fault statements, liveness), `CallRule` (the call rule over an abstract program, lookup facts), `F64Eval` (closed-number evaluation), `Eval` (`ts_eval`), `Bits` (the `ts_bits` set: bitwise operators on any operand), `DynNullish` (`=== undefined`/`null` and `x == null` on unknown values always answer), `DynOpt` (an unknown value passed to a `value?: unknown` parameter), `DynTypeof` (the answers of `typeof`, with the runtime type each implies). These three are reached from the root `StrictTS`, not from `Auto`: import `StrictTS` to have them in `ts_sym` |
| `StrictTS/Frontend/Prelude.lean` | notation used by generated code (macros that expand to plain IR) |
| `frontend/` | the TypeScript → Lean translator (`node frontend/dist/cli.js --help`) |
| `tests/corpus/` | differential test programs (and `reject/`: programs that must be rejected) |
| `tests/difftest/` | runner comparing Node's output with the Lean interpreter's |
| `tests/F64Diff.lean`, `tests/StrDiff.lean` | differential tests of the number and string models (against hardware doubles and Node) |
| `tests/proof/`, `examples/` | worked proofs |
| `examples/Modular/` | modular translator output of `examples/Summarize/loops.ts` (`LoopsMod/`, library `Modular`) and a proof over an abstract program (`LoopsModProof.lean`) with its instance for the program (`LoopsModProgram.lean`) |

## Building and running

```sh
lake build StrictTS.Proof.Tactics          # library (Lean 4.35, no Mathlib)
npm --prefix frontend ci                   # translator dependencies (typescript 5.9.3)
node frontend/dist/cli.js prog.ts --eval -o Prog.lean && lake env lean Prog.lean   # run in Lean
node tests/difftest/run.js                 # Node vs Lean on the corpus
lake exe f64diff all 1 250000              # binary64 model vs hardware doubles and Node
lake exe strdiff <cases>                   # string/number formatting model vs Node
```

## Validation

* **Semantics vs Node**: the translator corpus (139 programs, 40 rejection tests and two
  coverage-mode tests, `smoke` and `generics`; control flow, closures with boxing, functions and objects compared by identity, classes, records/unions/narrowing,
  dictionaries, `Map`/`Set` iteration under mutation, array callbacks, strings, bigint,
  exceptions/finally, async interleavings, `Promise.all` (arrays and tuples)/`allSettled`/`race`,
  unhandled rejections, timers,
  dynamic values, and external calls replayed from the Node run) — `PASS 180 / FAIL 0 / SKIP 0`
  in the latest run: the Lean interpreter prints exactly what Node prints.
* **Translation validation on public code** ([tools/validate/RESULTS.md](tools/validate/RESULTS.md)):
  every function that the es-toolkit and TheAlgorithms modules of `tools/public` emit and a driver
  can call (276 of 329; strict and dyn), run on the same 11,372 inputs (boundary values, `-0`/`NaN`
  keys in Maps and Sets, surrogates) under Node and under the Lean interpreter: result, return vs
  throw, console and final argument contents agree on 11,170; 201 are designed panics (unsound
  TypeScript typing), 1 is a documented model limitation. It found five bugs, fixed.
* **Scale**: a translated 320-line program (28 functions) elaborates in 2.6 s of CPU; each
  generated call lemma costs about 28 ms; the library builds in about two minutes on one core.
* **Numbers**: 0 mismatches against hardware doubles over ≈ 600k cases per operation
  (`+ - * / sqrt floor ceil trunc` comparisons, float32 rounding, bit patterns) and over ≈ 25k
  cases per JavaScript-specific operation against Node (`%`, `Math.round`, ToInt32 and all
  bitwise/shift operators, `Math.imul`, `clz32`, `min`/`max`, `Uint8ClampedArray`, BigInt
  conversions). Inside proofs, the closed-number evaluation agrees with hardware doubles on 400
  random `+ - * / %` cases (`tests/proof/F64EvalCheck.lean`, regenerated by
  `tools/f64eval/gen_check.py`; about 6 ms of kernel time per evaluation).
* **Strings and formatting**: 0 mismatches over 1,854,483 checks against Node 22
  (`Number::toString` on 431k doubles, `toFixed`/`toPrecision`/`toExponential`, `Number(s)`,
  `parseFloat`, `parseInt` in every radix, every string method).

## Trust base and limitations

* Proofs use Lean's kernel and the standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). `bv_decide` additionally trusts Lean's compiled LRAT checker.
* The translator is trusted (it is a syntax-directed translation; its output is validated by
  the differential corpus). Generated IR is readable and is the object of all proofs.
* Implementation-approximated functions (`Math.pow`, `Math.sin`, …, `localeCompare`,
  non-ASCII case mapping) are parameters (`Impl`); `Math.random`/`Date.now` are oracles in the
  world. Theorems hold for every implementation unless they assume otherwise. For `**` and
  `Math.pow` the semantics first gives the results ECMA-262 fixes (`F64.powSpec?`: `x ** ±0 = 1`,
  `x ** NaN = NaN`, infinities, zeros, `(±1) ** ±Infinity = NaN`, negative bases with non-integer
  exponents) and consults `I.pow` only for the remaining, implementation-approximated case.
* External (library and host) functions — Firestore, loggers, `fetch`, and for now `RegExp`
  and `JSON` — are typed calls `Expr.extern name args` answered by an oracle in the world
  (`World.ext`, indexed by the number of external calls made), and values of external types
  are opaque handles (`Ty.ext`). A theorem holds for every behaviour of the libraries; a
  library's contract is a hypothesis on `w.ext`. External code is assumed not to modify the
  program's own heap, and an asynchronous external call settles its promise at once (its
  continuation still runs as a microtask).
* Engine resource limits (heap exhaustion, V8's maximum string length of 2^29 - 24 code units)
  are not modelled: theorems are about runs that stay within them.
* Places where TypeScript's typing is unsound (out-of-bounds `a[i]` typed `T`, `x!` on
  `undefined`, holes, reads of uninitialised fields) are `panic` outcomes; a theorem about a
  run that returns `some (.ok …)` excludes them.
* Timers use a virtual clock: synchronous work takes no time, so programs whose output depends
  on how long computation takes between timers are outside the model.
* Not in v1: class inheritance and dynamic dispatch through interfaces, `RegExp`, generators,
  getters with side effects, `for … in`, top-level `await`, `Symbol`/`Proxy`/`Reflect`,
  `Object.*`/`JSON`, two-argument `then`, `Promise.any`, `Promise.allSettled` in `--strict`,
  `setInterval`/`clearTimeout`, methods used as values (see
  [frontend/README.md](frontend/README.md) for the translator's list).
  V8's own deviations from ECMA-262 (radix printing of large integers, `parseInt` in unusual
  radices) are reproduced as V8 does them.
