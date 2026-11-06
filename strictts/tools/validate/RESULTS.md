# Translation validation against Node (2026-10-24)

Every function that the public-project modules of [`tools/public`](../public/RESULTS.md) emit is
run on the same inputs under Node, on the original TypeScript, and under the Lean interpreter of
the StrictTS semantics, on the translator's output. The two runs agree on an input when four
observations are equal: the result value (printed deeply, `-0` and `NaN` distinguished), normal
return versus throw (with the error's name and message), the console output, and the contents of
the array, `Map`, `Set` and object arguments after the call.

**Result** (translator and semantics of this tree): of the 329 distinct functions that the
seven modules emit and a driver can call, 276 were run on 11,372 inputs. The two runs agree on
11,170 inputs; on 201 more the semantics stops with a *designed panic* where TypeScript's typing is
unsound and Node continues with `undefined` (below); 1 input differs, a documented model
limitation (`===` on two objects held in `unknown` values). The 80 other emitted functions, which
have no driver of their own (generic instances, lifted inner functions, a getter, a helper), all
run inside the validated drivers. Validating found five bugs, now fixed: three in the translator
(`Number.isInteger` and its siblings on values that are not statically numbers decided as
`false`; the property name `""` taken for a spread; `x !== x` on `unknown` objects stopping with
a panic) and two in the Lean runner (ASCII-only case mapping in `Impl.host`; a stack overflow when
printing long console lines). The strict and dyn translations of the 168 functions emitted in both
modes were both checked (165 translate to the same Lean text). Node corpus: PASS 140 / FAIL 0.

Measured on commit 91241e8 (translator, semantics and drivers as in its merge with master
ee94ab5, which changes none of them; a rerun of 9 of the functions there gives the same verdicts).

## Method

**Functions.** The modules are those of `tools/public` (es-toolkit v1.52.0 and TheAlgorithms
19b4ced; `--strict` and the default mode with dyn; the generic functions at `<number>`; the
functions with a callback parameter, called with one fixed pure callback), regenerated with the
translator of this tree. `--emit-lean` now also writes the list of the emitted functions with
their declarations (`Cov_*.funs.json`). Every emitted function that a driver can call (a
top-level function, a module-level arrow, a method or a constructor, not generic) is a target;
a function emitted in several modules is validated once, and once per translator mode when it
is emitted in both. Generic instances, lifted inner functions, getters and helpers have no
driver of their own and run inside the drivers of their callers (counted below).

**Inputs.** strictts-diff's type-directed generator (`tools/difftool/src/gen.ts`): every
parameter at its boundary values with the others at simple values (numbers `0, -0, NaN, ±Infinity,
-1, ±0.5, 2^31, 2^32, 2^53, -2^31-1, 1e21`; strings `"", " ", "😀", "\ud800", "NaN", "0", " 1 ",
"A", "__proto__"`; empty and one-element arrays, arrays repeating one element; the same special
value in every position), then random values (special numbers, random doubles from bit patterns,
strings mixing ASCII, accents, `ß`, `İ`, the Kelvin sign, BOM, NUL, astral characters and lone
surrogates, arrays with shared elements, Maps, Sets, records with optional fields present or
absent, class instances built by their constructors). Added by `tools/validate`: one parameter
at a time at an edge collection: Sets and Maps with the keys `0, -0, NaN, NaN, -0, 1` (and
`"", "\ud800", "😀", "\udc00", "", "__proto__"`), arrays with those elements, strings with
surrogate pairs and lone surrogates. 48 inputs per function at most (fewer for small input
spaces); inputs that take 50 ms or more under Node, or end in a timeout, stack overflow, crash or
host access there, are not sent to Lean (the interpreter is much slower).

**Runs.** strictts-diff's machinery (`tools/difftool`): the function is cut out of a copy of
its project with everything it depends on (a slice), and a driver is appended that builds each
input with literals, calls the function and prints the outcome and the arguments with printing
helpers written in the subset itself (so Node and Lean print through the same code). Node runs
the driver in a sandboxed child process (`Math.random()` and `Date.now()` answer 0, as the
oracles of Lean's `World.init` do). The translator translates the driver slice in each mode the
function is emitted in, and Lean evaluates it with `#eval runMain` (compiled code). The slice is
edited only in ways that do not change what runs: class members that the emitted module leaves
out (they are outside the subset, and no emitted function calls them) and overload signatures
(which have no runtime effect; the translator rejects calls of overloaded functions) are
removed. A driver that calls external functions (regular expressions, `JSON`,
`String.prototype.normalize`, `Date.now()`, host functions such as `ArrayBuffer.isView`) runs
under `tests/difftest`'s harness, which
records every external call with its arguments and answer; the Lean run replays those answers
in order and fails if the program makes a different call (`runMainTrace`).

**Designed panics.** Where TypeScript's typing is unsound, the semantics stops with a panic
instead of continuing with `undefined` (DESIGN.md §1.4): an out-of-bounds `a[i]` typed `T`,
`x!` on `undefined`, a checked cast of an `unknown` value to the wrong type, a hole. Node
continues. Such an input is counted as a *designed panic* when Lean's output up to the panic is
Node's output up to that point and the panic is one of those kinds; it is not a mismatch. A panic
ends the whole Lean run, so the inputs after it are run again in further drivers (in two halves
when there are many; up to 16 drivers per function).

## Results

<!-- BEGIN GENERATED (node tools/validate/validate.js report) -->
| module | emitted functions | with a driver | validated | inputs compared | agree | designed panics | mismatching inputs (functions) | not validated |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| es-toolkit strict | 96 | 94 | 94 | 3612 | 3612 | 0 | 0 (0) | 0 |
| es-toolkit dyn | 138 | 136 | 133 | 5390 | 5389 | 0 | 1 (1) | 3 |
| es-toolkit generic@number | 153 | 83 | 36 | 1540 | 1538 | 1 | 1 (1) | 47 |
| es-toolkit fixed callbacks | 96 | 49 | 49 | 2115 | 2115 | 0 | 0 (0) | 0 |
| TheAlgorithms strict | 76 | 74 | 71 | 2951 | 2751 | 200 | 0 (0) | 3 |
| TheAlgorithms dyn | 77 | 75 | 72 | 2999 | 2799 | 200 | 0 (0) | 3 |
| TheAlgorithms generic@number | 7 | 1 | 1 | 48 | 48 | 0 | 0 (0) | 0 |
| **distinct functions** | | **329** | **276** | **11372** | **11170** | **201** | **1 (1)** | **53** |

* Inputs generated for the validated functions: 11885; not sent to Lean: 4 slower than 50 ms under Node, 228 inconclusive there (timeout, stack overflow, crash, host access), 15 at an engine length limit.
* External calls replayed from the Node run: 31 functions.
* Strict and dyn translations of a function compared: 168 functions are emitted in both modes; their two drivers translate to the same Lean text in 165 validated cases (one Lean run), separately otherwise.
* Emitted functions without a driver of their own (generic instances, lifted inner functions, getters, helpers): 80 distinct; 80 run inside a validated driver.
* Inputs not compared because the drivers of a function (at most 16) all stopped at designed panics before reaching them: 219.
* Partially observable results: 29 validated functions return a value the printer shows only as `<value>`/`<union>` (a value of type `unknown`, a function, a union of objects), 38 more print some argument that way; for those, the comparison covers return vs throw, the console and the other observations.

| not validated: reason | functions |
|---|---:|
| inputs not generated — function-typed value | 47 |
| private method | 2 |
| inputs not generated — Error | 1 |
| no input finishes quickly under Node | 1 |
| driver outside the subset [ts2307]: Cannot find module 'node:stream' or its corresponding type declaration | 1 |
| no function unit at this declaration | 1 |

| mismatching function | inputs (mismatching) | differs in | first mismatching input: Node / Lean | cause |
|---|---:|---|---|---|
| projects/es-toolkit/src/compat/util/eq.ts:14 eq | 48 (1) | outcome, args, status | `eq({ isNaN: { hasOwnProperty: { isNaN: "hasOwnProperty" }, id: "ax", isNaN: "\\/éa9" } }, { isNaN: n`: return false ⏎ args <value> \| <value> / [PANIC comparison of values without identity] | model limitation: `===` on two objects held in `unknown` values, when both are records of the same type (records have no identity in StrictTS); Node compares references (two distinct objects: false) |

| function with designed panics | inputs | panics | panic | example input |
|---|---:|---:|---|---|
| public/mono/es-toolkit-dyn/mono_sample.ts:4 mono_sample | 48 | 1 | [PANIC array index out of bounds] | `mono_sample([])` |
| projects/thealgorithms-ts/data_structures/tries/tries.ts:49 Trie.find | 17 | 16 | [PANIC non-null assertion on undefined] | `new Trie().find(" ", true)` |
| projects/thealgorithms-ts/graph/bipartite_graph.ts:1 dfs | 16 | 16 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `dfs([], [], 1, 1)` |
| projects/thealgorithms-ts/graph/kosajaru.ts:2 getNodePriorities | 17 | 16 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `getNodePriorities([], [], [], 1)` |
| projects/thealgorithms-ts/graph/kosajaru.ts:37 gatherScc | 17 | 16 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `gatherScc([], [], 1, [])` |
| projects/thealgorithms-ts/maths/pascals_triangle.ts:17 pascalsTriangle | 27 | 14 | [PANIC array read at a non-index key] | `pascalsTriangle(0)` |
| projects/thealgorithms-ts/search/binary_search.ts:17 binarySearchIterative | 42 | 14 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `binarySearchIterative([2147483647, -1], 2147483647, 2147483647, -25)` |
| projects/thealgorithms-ts/search/binary_search.ts:43 binarySearchRecursive | 41 | 15 | [PANIC array read at a non-index key], [PANIC array index out of bounds] | `binarySearchRecursive([2], -8, -8, -0)` |
| projects/thealgorithms-ts/search/fibonacci_search.ts:16 fibonacciSearch | 31 | 15 | [PANIC array index out of bounds] | `fibonacciSearch([], 1)` |
| projects/thealgorithms-ts/search/interpolation_search.ts:12 interpolationSearch | 32 | 14 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `interpolationSearch([], 1)` |
| projects/thealgorithms-ts/sorts/cycle_sort.ts:42 CountSmallerItems | 46 | 8 | [PANIC array read at a non-index key] | `CountSmallerItems([-7, -7, -7, -7, -7], -54, -758)` |
| projects/thealgorithms-ts/sorts/heap_sort.ts:36 heapify | 43 | 13 | [PANIC array read at a non-index key], [PANIC array index out of bounds] | `heapify([], -Infinity, 1)` |
| projects/thealgorithms-ts/sorts/heap_sort.ts:56 swap | 18 | 16 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `swap([], 1, 1)` |
| projects/thealgorithms-ts/sorts/quick_sort.ts:8 partition | 19 | 16 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `partition([], 1, 1)` |
| projects/thealgorithms-ts/sorts/quick_sort.ts:61 QuickSort | 44 | 9 | [PANIC array read at a non-index key], [PANIC array index out of bounds] | `QuickSort([1, -8], 1)` |
| projects/thealgorithms-ts/sorts/quick_select.ts:13 QuickSelect | 44 | 2 | [PANIC array index out of bounds], [PANIC array read at a non-index key] | `QuickSelect([], NaN, 1, 1)` |
<!-- END GENERATED -->

## Mismatches and their causes

Found by this validation and fixed (the runs above use the fixed tree; the corpus and every
example translate exactly as before):

1. **Translator: `Number.isInteger`, `isSafeInteger`, `isFinite`, `isNaN` on a value that is not
   statically a number.** They were decided as `false` whenever the argument's static type was not
   `number`: wrong for `unknown`/`any` (es-toolkit's lodash-compatible `isLength`, `isInteger`,
   `isSafeInteger` and `isFinite` returned `false` for every safe integer: `isLength(-0)` gave
   `false`, Node `true`) and, in both modes, for `number | undefined` and unions that hold
   numbers. Now decided on the runtime value (`numberPred` in `frontend/src/exprs.ts`).
2. **Translator: the property name `""`.** An object literal property named by the empty string
   was taken for a spread (its name was tested for truthiness), so `{ "": "x" }` was rejected as
   "spread of string" (`frontend/src/exprs.ts`).
3. **Translator: `x !== x` on an `unknown` value that holds an object.** The NaN idiom (`if (a !==
   a) return 4;` in es-toolkit's `getPriority`) compared the value with itself through the
   dynamic `===`, which stops with a panic for records (they have no identity). With one variable
   on both sides `x === x` is false exactly for NaN, whatever the value, and the translator now
   lowers it so for the types without `===` in the IR (unknown values, records, tuples); every
   other type keeps its `===`.
4. **Runner: case mapping of non-ASCII strings.** The semantics leaves non-ASCII case mapping to
   the `Impl` parameter (theorems hold for every implementation), and `Impl.host`, which `runMain`
   uses, mapped only ASCII letters: `upperFirst("ß")` gave `"ß"` (Node `"SS"`), `lowerFirst("İaa")`
   gave `"İaa"` (Node `"i̇aa"`). `Impl.host` now does the Unicode default case conversion
   (`StrictTS/Str/Case.lean`: full mappings and Final_Sigma) with tables generated from Node's ICU
   (`tools/gen_case_tables.js`, `StrictTS/Str/CaseTables.lean`, Unicode 17). `tools/case_check.js`
   compares it with Node on 32,985 strings (every code point that has a case mapping, and random
   strings over Greek sigmas, combining marks, ligatures, `İ`/`ı`, Georgian, Cherokee, Deseret and
   lone surrogates): 0 disagreements.
5. **Runner: long console lines.** `JSStr.toLeanString` was not tail recursive: printing the
   result of `generateParentheses` overflowed the interpreter's stack.

Tooling fixed on the way: the difftest's trace replay (`tests/difftest/run.js`) inserted the
recorded calls with `String.replace` and a string as replacement, so a recorded `$&`
(escapeRegExp's replacement pattern) was expanded into the matched text; the difftest harness now
also records host functions that the translator calls as externs by name (`STRICTTS_TRACE_EXTRA`:
`ArrayBuffer.isView` in `isTypedArray`); strictts-diff's drivers give empty `Map`/`Set` literals
type arguments (`new Map()` is a `Map<any, any>`, which the translator rejects) and assert the
nested values of literals for `unknown` parameters to `unknown` (TypeScript typed some as unions
the translator cannot convert).

What remains:

* **Model limitation** (1 input): es-toolkit's `eq` computes `value === other` for two `unknown`
  values; for two distinct object literals whose runtime values are records of one type, the
  dynamic `===` stops with a panic, because StrictTS records have no identity and the semantics
  cannot tell one object from two equal ones (Node: `false`). Answering `false` when the two records
  differ would remove this case; that is a change of the semantics of `===` on unknown values and
  is not made here.
* **Designed panics** (201 inputs, 16 functions): helper functions called with arbitrary index
  arguments: `partition(arr, lo, hi)`, `swap`, `heapify`, binary and interpolation searches with
  `start`/`end` outside the array, graph helpers with node numbers outside the adjacency list,
  `pascalsTriangle(0)`, `Trie.find` with `!` on a missing child, `sample([])`. Node reads
  `undefined` and continues; the semantics stops (DESIGN.md §1.4), with Lean's output up to the
  panic equal to Node's in every case. 219 later inputs of these functions were not compared,
  because all drivers of the function stopped before reaching them.
* **Designed panics confirmed in Node** (`validate.js run --single --record`, `sites`, `checked`):
  with one driver per input after a panic, all 721 inputs of the 16 functions are compared (337
  agree, 384 designed panics, 0 mismatches; of the 219 inputs not compared above, 36 agree and 183
  are designed panics). On the checked build of tools/public/node (reads checked against their
  TypeScript types; `Math.random()` answering 0 as in Lean), all 384 fail at the read where Lean
  panics (the last position printed by markers inserted before every checked read in the Lean
  run), and none of the 337 agreeing inputs fails a check.
* **Partially observable results**: the printing helpers have no form for values of type
  `unknown`, functions and unions of object types; those print as `<value>`/`<union>` on both
  sides (29 validated functions return such a value, 38 more take such an argument), so for them
  the comparison covers return versus throw, the console output and the other observations, not
  the value itself.
* **Node side**: no mismatch came from Node. Inputs that Node cannot run conclusively (timeouts,
  stack overflows, host access) or runs slowly are not compared (counted above), and
  `Math.random()`/`Date.now()` answer 0 in both runs (`Date.now()` is replayed in drivers with
  external calls).
* **Not validated** (53 functions): 47 have a parameter of function type (all of them `<number>`
  wrappers of generic functions that take a callback; the 49 fixed-callback wrappers, all
  validated, call such functions with one fixed pure callback), one takes an `Error`, two are private methods, one needs `node:stream` types, one is an
  implicit constructor (`TrieNode`, no declaration to call; it runs inside `Trie`'s drivers), and
  for one (`toolkit`, a namespace object built from re-exports) no input finishes under Node in the
  slice.

## Private code: another project and a second project (aggregates only)

The same validation on the ten modules emitted from the two private projects (strict and dyn
modes), with the translator, semantics and drivers of this tree. Names, paths and values from
that code appear nowhere in this repository: the drivers, the results and the per-function
details stay in an untracked work directory, and this section has counts only (written by
`validate.js report` in private mode).

**Differences from the public run.**

* *Sources.* Read-only copies of the snapshots behind the coverage numbers in README
  (`.env.example` and certificate files left out of the copy); the modules are emitted from
  those copies, never from the live trees. Every slice is copied into the work directory before
  anything runs.
* *Sandbox.* Every Node run (the inputs, the drivers, and the harness that records external
  calls) is one process with no network, no writes, no child processes and file reads only
  inside the work directory:

  ```
  bwrap --unshare-net --die-with-parent --ro-bind / / --dev /dev --proc /proc -- \
    node --permission --allow-fs-read=<work dir> --stack-size=984 --max-old-space-size=1024 <runner> <message file>
  ```

  with an environment of `PATH` and `LANG` only (plus `STRICTTS_TRACE` and
  `STRICTTS_TRACE_EXTRA` for drivers with external calls). Node's permission model grants no
  writes, child processes, worker threads or addons; bwrap's empty network namespace removes the
  network. strictts-diff's runner (child.js: a vm context with its own module loader, no fs or
  network globals) is copied into the work directory and driven through a shim instead of an IPC
  fork. No external package is imported.
* *Excluded and counted.* Slices that import a package or any non-relative module (they would
  need the project's dependencies); slices that read `process.env`; drivers that call an
  external function other than a pure built-in (only regular expressions, `JSON`,
  `String.prototype.normalize`, URI coding and `ArrayBuffer.isView` are replayed: recording them
  calls nothing outside); drivers whose record of external calls exceeds 2 MB; string literals
  mined from the code that look like keys or tokens (never used as inputs).
* *Driver size.* Inputs of large record types make a driver's main function megabytes of Lean
  text (each literal writes out every record and union type at every node), so above 150 KB a
  driver keeps its first inputs (boundary values first, at least 8); a driver of more than
  400 KB of Lean text in all is not run (counted).
* *Type environment of drivers.* A slice that uses Node's or the browser's globals is
  translated with Node's or the DOM's declarations, as its module was.

**Result.** Of the 3,900 distinct functions that the private modules emit and a driver can call,
2,081 were run on 84,888 inputs. The two runs agree on 81,827 inputs; on 2,957 more the semantics
stops with a designed panic (below); 104 inputs of 23 functions differ, every one of them
explained below. Validating found four translator bugs (three fixed with this section, the
fourth in b3e3a34) and three semantics and runner differences (fixed in b4e9d04).

| private code (another project + a second project) | functions with a driver | validated | inputs compared | agree | designed panics | mismatching inputs (functions) | not validated |
|---|---:|---:|---:|---:|---:|---:|---:|
| emitted in strict mode | 2485 | 1403 | 57867 | 57179 | 612 | 76 (16) | 1082 |
| emitted in dyn mode | 3900 | 2081 | 84888 | 81827 | 2957 | 104 (23) | 1819 |
| **distinct functions** | 3900 | 2081 | 84888 | 81827 | 2957 | 104 (23) | 1819 |

* Emitted functions: 4,031 (dyn) and 2,550 (strict) in ten modules; 112 distinct have no driver of
  their own (generic instances, constructors of mutable records, getters, lifted functions,
  helpers), 17 of them run inside a validated driver.
* Inputs generated for the validated functions: 94,043; not sent to Lean: 12 slower than 50 ms
  under Node, 145 inconclusive there (timeout, stack overflow, crash, host access), 23 at an
  engine length limit, 4,448 over the driver size cap (218 functions with inputs of large record
  types).
* External calls replayed from the Node run: 834 functions (pure built-ins only).
* Designed panics: 2,957 inputs of 271 functions: `x!` on undefined and checked casts (210
  functions), an inherited `Object.prototype` key read from a dictionary (27), array reads at a
  non-index key (23) or out of bounds (22), assignment to `__proto__` (2), a typed-array read at a
  non-index key (1). 4,513 later inputs of those functions were not compared (all their drivers
  stopped at panics before them).
* Strict and dyn translations: the 2,485 functions emitted in both modes translate to the same
  Lean text in 1,402 of their 1,403 validated cases.

| not validated | functions |
|---|---:|
| imports a package or a non-relative module (not run) | 653 |
| calls an external function other than a pure built-in (excluded) | 457 |
| not reached in the time budget (the pass that ran again the functions affected by fixes made during the run) | 203 |
| driver not translatable: TypeScript errors in the slice (types of packages and hosts missing: 104; narrowings that differ in the slice: 15) | 119 |
| inputs not generated (function-typed parameters 101, `RegExp` 6, `DataView` 1, `Intl.DisplayNames` 1) | 109 |
| driver not translatable: outside the subset (tagged templates, i.e. `String.raw` regex sources, 50; effects on the program's own state 19; other 18) | 87 |
| driver too large for the Lean time limit (not run) | 61 |
| private method | 58 |
| no function unit at this declaration | 34 |
| reads `process.env` (excluded) | 30 |
| no input finishes quickly under Node | 6 |
| record of the external calls too large to replay (excluded) | 1 |
| Lean ran out of memory (a typed array that V8 allocates lazily) | 1 |

| mismatches by cause | functions | inputs |
|---|---:|---:|
| model limitation: last bits of an implementation-approximated Math function (`Impl.host` uses the C library, V8 its own) | 7 | 23 |
| model limitation: `String()` of an object with its own `toString`/`valueOf` panics (Node throws a TypeError) | 5 | 23 |
| translator bug: `s[i]` on a string with a negative, fractional or NaN index read a character (fixed in b3e3a34, after this run) | 2 | 19 |
| semantics (fixed in b4e9d04): the RangeError text for a typed-array length is not V8's | 3 | 11 |
| model limitation: `toString(radix)` of a non-integer (implementation-approximated in ECMA-262) | 1 | 10 |
| replay limitation: external calls inside a sort comparator (the order of the comparator's calls is implementation-defined) | 1 | 6 |
| model limitation: `localeCompare` is locale-dependent (`Impl.host` compares code units, Node uses ICU collation) | 1 | 4 |
| assumption violated (DESIGN.md §1.7): an external answer asserted with `as T` is not a T | 1 | 3 |
| runner (fixed in b4e9d04): `Impl.host` computed `Math.log1p` as `log(1 + x)` | 1 | 3 |
| a property of an array other than an index or length read through unknown panicked (b4e9d04: undefined unless inherited) | 1 | 2 |

**Found and fixed.**

1. *Translator: `JSON.stringify`'s answer typed `string`* (c84b97d). JavaScript answers undefined
   for undefined, a function or a symbol at the top level (and when `toJSON` or a replacer gives
   undefined); the oracle could not give that answer, so a replay raised an exception that the
   program's own `catch` handled. The answer is now `string | undefined`, and undefined where a
   string is needed is a designed panic. Corpus `json_stringify_undefined`.
2. *Translator: an optional unknown holding an unknown undefined* (ff73009). A parameter `T |
   undefined` at T = unknown, given a `Map` value or array element of type unknown that is
   undefined, took the defined branch of `x === undefined`. Corpus `generic_opt_unknown`. (No
   emitted function changes; the drivers' printing helpers did.)
3. *Translator: optional chaining on any/unknown* (42bf6df). Each `?.` link was a plain property
   read, so `(p as any)?.a?.b` threw a TypeError when `p.a` was undefined. Corpus
   `dyn_optional_chain`.
4. *Translator: `s[i]` on strings* (fixed in b3e3a34, with the proof-side follow-up; the run
   above used the translator before it). `s[i]` was lowered to `String.prototype.at`, which
   truncates the index and counts negative ones from the end; JavaScript gives undefined for any
   key that is not an array index.
5. *Semantics and runner* (b4e9d04, landed after notice to the peers): the
   RangeError text for typed-array lengths; reads of array keys through unknown (undefined unless
   inherited) and `in` on arrays (true for inherited keys); `Impl.host`'s `log1p`, `expm1` and
   `hypot`.
6. *Tooling.* The difftest harness cut records of external calls at about 290 KB (a write to a
   pipe in an exit handler); strictts-diff took the library's anonymous mapped type of `Record<K,
   V>` for an unsupported library type (no inputs for 210 functions); drivers did not assert array
   and object literals nested at type unknown, and lacked Node's and the DOM's declarations for
   slices that use those globals; removing class members that the module leaves out broke
   `implements` clauses.

Measured with the translator of 42bf6df (master 5b7e08a with fixes 1-3) and the semantics before
b4e9d04, on modules emitted from those copies; the tooling fixes were installed
during the run, and every function they could affect was run again afterwards, except the 203
counted above as not reached. To repeat it (with `CM_ROOT` and `NP_ROOT` the snapshot copies, and
the modules emitted from them into `tests/coverage/lean/v3` and `v3/strict` by
`frontend/dist/cli.js --coverage [--strict] --emit-lean`):

```sh
export VALIDATE_SUITES=tools/validate/suites_private.json VALIDATE_WORK=scratch/validate_private VALIDATE_LEAN=tests/coverage/lean/v3 CM_ROOT=<another project copy> NP_ROOT=<a second project copy>
tools/run.sh 0.1 300 node tools/validate/validate.js plan
VALIDATE_LEAN_BATCH=2 VALIDATE_LEAN_TIMEOUT=150 VALIDATE_MAX_JOB_BYTES=400000 ROUNDS=60 tools/validate/run_all.sh
tools/run.sh 0.1 300 node tools/validate/validate.js report            # WORK/AGGREGATES.md (counts), WORK/DETAILS.md (untracked)
```

## Reproduce

From the root of a checkout or of a `git archive` copy (every path below is relative to it; the
outputs go to its `scratch/`):

```sh
npm --prefix frontend ci                                             # typescript 5.9.3 (translator, strictts-diff)
tools/run.sh 1 1500 lake build StrictTS                              # the Lean library the drivers run on
tools/public/fetch.sh                                                # the projects at their pinned commits
tools/run.sh 0.3 590 tools/public/coverage.sh strict es-toolkit      # also: dyn es-toolkit, strict and dyn thealgorithms-ts
tools/run.sh 0.3 590 tools/public/mono_emit.sh dyn es-toolkit mono   # also: dyn es-toolkit cb, dyn thealgorithms-ts mono
tools/run.sh 0.1 300 node tools/validate/validate.js plan
tools/validate/run_all.sh                                            # rounds of three guarded shards until none is left
tools/run.sh 0.1 300 node tools/validate/validate.js report          # this file's tables, tools/validate/results.tsv
# the functions with designed panics again, then the panics on Node's checked build (built when missing)
VALIDATE_WORK=scratch/validate_panics tools/validate/run_all.sh --panicked --single --record
VALIDATE_WORK=scratch/validate_panics tools/run.sh 0.3 590 node tools/validate/validate.js sites     # repeat until "0 … left"
VALIDATE_WORK=scratch/validate_panics tools/run.sh 0.3 590 node tools/validate/validate.js checked
```

`tools/validate/results.tsv` has one row per function and module (inputs compared, agreements,
designed panics, mismatches, reason when not validated); `scratch/validate/` keeps the drivers,
the Lean files and their outputs.
