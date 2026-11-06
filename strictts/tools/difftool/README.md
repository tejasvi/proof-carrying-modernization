# strictts-diff: semantic diff for TypeScript

For every function that changed between two versions of a TypeScript project, `strictts-diff`
reports one of

* **PROVED**: a Lean theorem says that the old and the new function have the same behaviour on
  every argument list and in every world (heap, console, job queue, timers), and Lean checked it
  without `sorry` (`#print axioms` is part of the check; proofs that use `bv_decide` are flagged
  because they trust Lean's compiled LRAT checker);
* **REFUTED**: a concrete input on which old and new behave differently, found by differential
  fuzzing in Node, re-checked in fresh processes, and (when the function is inside the StrictTS
  subset) confirmed by running both translated functions on the same input under the Lean
  semantics. `REFUTED*` in the table means the counterexample is confirmed in Node only (the
  function is outside the subset, or its driver could not be translated);
* **UNKNOWN**, with the reason: outside the subset (rule ids), inputs of a type that is not
  generated, external module dependencies, signature change, proof not found (with the shape of
  the residual goal: loops, array callbacks, Map operations, allocation, number or string
  reasoning), Lean timeout.

```sh
tools/run.sh 0.5 590 node tools/difftool/dist/cli.js OLD NEW [--details] [--json out.json]
#   OLD / NEW: a file, a directory, or git:REV:path (with --repo DIR)
tools/run.sh 0.5 590 node tools/difftool/dist/cli.js bench tests/equiv-bench
tools/run.sh 0.5 590 node tools/difftool/dist/cli.js validate tests/corpus/*.ts
tools/run.sh 0.5 590 node tools/difftool/dist/cli.js history --repo REPO --out tests/history --phase scan|run   # gitignored: local only
```

Build: `tools/run.sh 0.1 300 node frontend/node_modules/typescript/bin/tsc -p tools/difftool`
(the compiled `dist/` is committed, like `frontend/dist/`). Exit status: 0 = nothing refuted,
1 = some function refuted (or, for `bench`, a wrong verdict), 2 = usage or internal error.

## What the verdicts guarantee

* REFUTED rests on Node, the ground truth: the inputs are values of the old parameter types that
  the new parameter types also accept (a structural check; otherwise the function is UNKNOWN with
  "signature changed"), both runs completed (no timeout, stack overflow, crash, or access to a host
  global such as `process` that the sandbox does not provide), and the difference reproduces in
  fresh processes. A Node counterexample always takes precedence; no proof is attempted then.
* PROVED is equality in the StrictTS semantics for every argument list and every world, for every
  `Impl` (Math functions, locale); or, when the report says "allocated-arguments", for every
  world in which the argument arrays, maps and sets are allocated cells below the allocation
  counter (arrays shorter than 2^32), which every state of a real run satisfies; or, when it
  says "allocated-arguments-strlen", in addition only for string arguments of at most 2^53 - 1
  code units, the maximum length of an ECMAScript String (ECMA-262 6.1.4). The model's strings
  have no bound, and a longer length would round when it becomes a number
  (`s.slice(0, p.length) === p` then differs from `s.startsWith(p)` in the model only). When it
  says "allocated-arguments-objects", the object arguments (class instances) are also allocated
  cells with initialised fields, and their array fields allocated cells with fewer than 2^32 - 1
  elements (room for one `push`). Where
  TypeScript's typing is unsound (`a[i]` out of bounds,
  `x!` on `undefined`) the semantics panics; the theorem then says that both versions panic at the
  same point after the same effects, but it does not compare what JavaScript would do after that
  point (it would continue with `undefined`). Such inputs are covered by the fuzzer, which runs first.
* Equality of whole worlds includes the allocation counter: refactorings that allocate a
  different number of objects are not provable with the default statement (UNKNOWN, "allocation
  differs") even when they are observationally equivalent.
* PROVED with statement "observational" is clearly WEAKER than all of the above: it is not an
  equality of worlds. In every world with allocated array/Map/Set arguments and string arguments
  of at most 2^53 - 1 code units, both versions diverge, or both end with the same result (for
  results without references: numbers, strings, booleans, errors, enums, and records, tuples,
  optionals and unions of these) or with the same caller array or two freshly allocated arrays
  with equal contents (for arrays of such values), the same console output, the same contents of
  every cell below the caller's allocation counter, and the same numbers of `Math.random()`,
  `Date.now()` and external-call answers consumed (`Obs.ObsEq` / `Obs.ArrObs` of
  StrictTS/Proof/Obs.lean, copied from equiv-lean). The cells the callee allocated (other than
  the returned array) and the allocation counter are ignored, and the asynchronous state is not
  compared, so the statement is only attempted for functions without promises, `async`, timers or
  microtasks, after every equality statement failed.
* What is compared can be narrower than the whole functions, and the notes say so:
  - A generic function is compared at one instance (wrapper `__difftool_inst`, e.g. `T := number`;
    the instance table is `INSTANCES` in `diff.ts`).
  - When the new version widens the parameters (a parameter made optional, a union widened), the
    comparison is on the old version's inputs (wrapper `__difftool_compat`, which takes the old
    parameters and calls the new version).
  - When the declared return type changes, the comparison is at the other version's return type
    (wrapper `__difftool_ret`).
  - A wrapper passes a destructured parameter whole, under a name of its own (`__difftool_p<i>`).
  - A generic version compared with a non-generic one, or two generic versions at different
    instances, is compared when the wrappers' translated signatures agree.
* The statement `old-no-panic` is WEAKER still and is not an equivalence: for every argument list
  and world, the two runs are equal or the old run panics. Where the old version panics, the new
  one may do anything. It covers changes that keep every in-type run of the old version and only
  replace a designed panic, e.g. a return type widened from `T` to `T | undefined`. Since 10-27
  ~09:10Z such a function has verdict UNKNOWN with this proof attached, never PROVED.

## Pipeline

1. **Specs** (`spec.ts`): OLD and NEW are materialized into a scratch directory: the named files
   plus every file reachable through relative imports (`git show` for `git:REV:path`, read-only).
2. **Pairing** (`units.ts`): top-level functions, `const f = (…) => …`, class methods and
   constructors are paired by module and qualified name; a function is *changed* when its
   comment- and formatting-free printed text differs.
3. **Slices** (`slice.ts`): each changed function is cut out of its project with everything it
   depends on (functions, classes, types, module variables and the module statements that
   initialise them), as a pruned copy of the original files that keeps the import structure
   (re-exports `export * from` and `export { a } from`, e.g. in index files, keep the names the
   slice declares).
   External package imports make a slice non-runnable (UNKNOWN). The *proof* slice additionally
   inlines module constants with literal initializers and is recomputed.
4. **Fuzzing** (`typedesc.ts`, `gen.ts`, `child.ts`, `fuzz.ts`): the parameter types (from the
   TypeScript checker) drive input generation: special numbers (NaN, ±0, ±Infinity, 2^31, 2^32,
   2^53 neighbours, fractions), strings (empty, whitespace, astral characters, lone surrogates,
   `__proto__`, numeric strings, literals mined from both versions), bigints, arrays with
   duplicates, tuples, records with optional fields present or absent, unions, string-literal
   enums, Map/Set, class instances built by their constructors; values are re-used across
   parameters and elements of one input (so `includes(x)` meets `x`). Both versions run in
   their own child process (`vm` context, fresh module instances per input, per-call timeout,
   virtual timers, `Math.random`/`Date.now` fixed at 0 as in Lean's `World.init`, captured
   console). The observation is the outcome (return value, thrown error name and message,
   promise resolution or rejection), console output, unhandled rejections, and the state of the
   arguments (and receiver) after the call, printed canonically (NaN equals NaN, -0 differs from
   0, arrays/Maps/Sets/class instances keep their sharing, plain objects compare structurally).
   Differences only in object key order or undefined-valued keys are reported as a note, not as
   a counterexample (StrictTS cannot observe them). Timeouts, stack overflows and crashes are
   never counted as differences. A difference is shrunk (smaller arrays, simpler numbers and
   strings, absent optional fields) and must reproduce in fresh processes.
5. **Lean** (`driver.ts`, `lean.ts`): a counterexample is confirmed with a *driver*: TypeScript
   appended to the slice that builds the input with literals, calls the function and prints
   outcome and arguments with subset-only printing helpers. The same driver runs under Node and,
   translated with `--eval`, under `runMain`; REFUTED is Lean-confirmed when Lean's outputs equal
   Node's for both versions and differ from each other (any Lean/Node difference on a driver is
   reported as a translator or semantics mismatch). Without a counterexample the proof slices are
   translated into namespaces `Old_<id>` / `New_<id>` and the theorem

   ```lean
   theorem equiv_<id> (I : Impl) : ∀ (vs : Vals Old_<id>.TT [args]) (w : World Old_<id>.TT),
       JS.exec (callFun I Old_<id>.program Old_<id>.«fRef» vs) w =
         JS.exec (callFun I New_<id>.program New_<id>.«fRef» vs) w
   ```

   is attempted (only when the translated globals and module bodies are identical, so that the
   ∀-world statement speaks about the real module state). When the function takes arrays, maps
   or sets, a second theorem `equiv_<id>_wf` states the same equality for every world in which
   those arguments are allocated cells (`hw : w.heap.get? (.arr T, a) = some c`,
   `hn : a < w.next`, `hs : c.size < 2 ^ 32`), which holds in every state a run reaches; loops that
   allocate (a push loop against `map`/`filter`) or that count over an array need these facts.
   When it takes strings, a third theorem `equiv_<id>_wfs` adds `hl : s.length < 2 ^ 53` for each
   string argument (the maximum String length), which string lengths that become numbers need.
   When it takes class instances, a fourth theorem `equiv_<id>_wfo` states the object cell with its
   field values (`ho : w.heap.get? (.obj C fields, a) = some …`) and the array fields as allocated
   cells with fewer than 2^32 - 1 elements, for methods that `push` to a field and then loop over
   it. The new version's type table and class field lists are emitted as aliases of the old ones
   when their text is the same, so that both versions read objects under the same heap key.
   When none of these equalities is proved and the result holds no references (or is an array of
   such values) and neither version schedules asynchronous work, a second Lean pass attempts
   `equiv_<id>_obs` (statement observational, files `obs_NN.lean`), with the hypotheses of
   `_wf` and `_wfs`:

   ```lean
   Obs.Equiv (Obs.ObsEq w.next)     -- or Obs.ArrObs w.next for an array result
     (JS.exec (callFun I Old_<id>.program Old_<id>.«fRef» vs) w)
     (JS.exec (callFun I New_<id>.program New_<id>.«fRef» vs) w)
   ```

   Its script is the default one where `ts_auto` also gets the simprocs `dtFreshRead` (an
   argument cell below `w.next` read through the callee's allocations at `w.next + k`) and
   `dtToIntOfNat` (a position bounded by 2^53 through `omega`, e.g. in `s.charAt(i)`), the
   `@[simp]` lemmas of Obs.lean reduce the relation to equalities of values and of caller cells,
   and a last closer adds the fold lemmas of a reversed string (`foldrFstUnit`, `foldr_val_str`,
   `foldl_append_eq_foldr` in StrictTS/Proof/LibLemmas.lean: `join("")` of the reversed parts
   against a backwards `charAt` loop).
   PROVED names the strongest statement that was proved. Both proof scripts are CLI options (`--tactic FILE`,
   `--tactic-wf FILE`; placeholders `{OLDCALL} {NEWCALL} {OLD} {NEW} {F} {DESTRUCT} {DEFS}`); the
   defaults (`intro vs w` first for the ∀ statement) are

   ```lean
   ts_destruct                          -- Vals, records, tuples, optionals, enums (StrictTS.Proof.Literals)
   ts_enum_cases                        -- enum values: one case per member (idem)
   ts_cells                             -- argument cells: present (hcell) or dangling (idem)
   all_goals first
     | (dt_unfold; first | rfl | (simp [ts_sym, *]; done)
                         | (dt_typeof_cases; all_goals first | rfl | (simp [ts_sym, *]; done) | …))
                                        -- cheapest first: the alternatives share one heartbeat budget;
                                        -- dt_typeof_cases splits on the answer of `typeof` (DynTypeof)
     | (dt_int_guard; dt_unfold; dt_int_cases; dt_eval_calls; all_goals dt_eval_loops)
                                        -- a number validated as an integer in 0 … m (m ≤ 64): each value
     | (ts_auto [Array.size_push]       -- StrictTS.Proof.Auto: unfold, summarize loops/callbacks, simp;
        all_goals (subst_vars; first | (simp [ts_sym, *]; done) | (simp_all [ts_sym]; done)))
                                        -- the goals it leaves, with their case equations
     | (dt_unfold; first | rfl | (simp [ts_sym, *]; done))         -- e.g. dangling cells
     | (dt_auto                         -- ts_auto without its final simp, then case splits
        all_goals (repeat' (first | ts_summarize | ts_callbacks | dt_ite_split | dt_heap_split))
        all_goals first | rfl | dt_contra | ts_int32 | dt_int32 | (simp [ts_sym, *]; done)
                        | grind | omega | (simp_all; done)
                        | (simp_all [dt_size_le_lit, …, dt_pop_small]; done)   -- array sizes vs numerals
                        | fail "difftool: residual goal")
     | (dt_unfold                        -- the same without summaries (identical loops close by rfl)
        all_goals (repeat' (first | dt_ite_split | dt_heap_split))
        all_goals first | … | fail "difftool: residual goal")
   ```

   `ts_destruct`, `ts_enum_cases`, `ts_cells` and the `arrayIndexNumeral` simproc are in
   StrictTS/Proof/Literals.lean, the `Conv.strictEq` equations in StrictTS/Proof/Unfold.lean;
   the `dt_*` glue tactics are in `lean/DiffPrelude.lean`, included after `import StrictTS` in
   every generated file. `dt_heap_split` rewrites with a hypothesis that already answers a heap
   lookup (the `hw` of the allocated-arguments statements), so the cell keeps its size bound;
   otherwise it splits on the lookup. When no other statement is proved, the second pass also
   attempts `equiv_<id>_np` (statement old-no-panic, above):
   `old = new ∨ ∃ s w', old = some (.error (.panic s), w')`. Lean runs in batches (one process per
   batch; a timed-out or crashed batch is retried unit by unit).
6. **Report** (`report.ts`, `interface.ts`): table (function, verdict, evidence) and the JSON result
   `strictts-diff/v1` (frozen; see [INTERFACE.md](INTERFACE.md), checked by `strictts-diff selftest`).

`validate FILE.ts…` runs every function of the files on random inputs (those that finish quickly
under Node) through one driver per function under Node and under Lean, and reports mismatching
inputs reduced by a few shrinking rounds. `history` scans a repository's commits (read-only `git
log`/`git show`), classifies every changed function (external modules, signature change, input
types, subset rules, in subset), extracts self-contained pairs (slices only, after a check for
text that resembles credentials) and runs the diff on them. A pair is in the subset only when both
versions translate and contain the target function (rule `target-not-translated` otherwise; a
generic target is checked through its instance wrapper). The library-history audits made with it
(es-toolkit, remeda) are in `r6*/`, each with its results file, tables and evidence manifest.

## Benchmark

`tests/equiv-bench/NN_name/{old.ts,new.ts,expected}`: 67 refactorings, 44 equivalent and 23
subtly non-equivalent; `expected` starts with `equivalent` or `different`.

## Open items

* Benchmark (10-24, 774ed50): 43/44 equivalences proved (32 for every world, 5 allocated-arguments, 2 allocated-arguments-strlen, 1 allocated-arguments-objects, 3 observational: 32, 36 and 44), 23/23 differences refuted (21 confirmed by Lean), 0 wrong; the open equivalence (34) and what it needs are listed in tests/equiv-bench/README.md.
* Functions whose results can hold references to fresh cells (arrays of arrays, maps, sets, objects, functions) get no observational statement: comparing such results needs a renaming of the addresses the callee allocates, which is not formalised (likewise in equiv-lean's Obs.lean).
* The concrete evaluation of pair 23 unrolls the new version's loop one iteration at a time; a summary of decreasing counted loops would make it cheaper.
