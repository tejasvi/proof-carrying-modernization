# strictts-diff interface (frozen, v1)

strictts-diff is the TypeScript component of verif-orchestrator: given two versions of a
TypeScript project, it reports for every changed function whether old and new are equivalent
(PROVED), differ on a concrete input (REFUTED, REFUTED*), or neither could be established
(UNKNOWN). This file fixes how it is called and what it returns. The result format is
`strictts-diff/v1`; its JSON Schema is [`schema/strictts-diff-v1.schema.json`](schema/strictts-diff-v1.schema.json).

## Invocation

```sh
node tools/difftool/dist/cli.js [diff] OLD NEW [options]
```

run from the repository root (the tool locates the translator in `frontend/` and the Lean build
in `.lake/` relative to its own path, so the working directory only matters for relative specs
and `--repo`). Requirements: Node ≥ 22, `frontend/node_modules` installed, and for the Lean stage
the library built (`lake build StrictTS`) with `lake`/`lean` on `$HOME/.elan/bin`; without the
Lean build the tool still runs (fuzzing only, every non-refuted function UNKNOWN with
`lean-disabled`). In this repository every command runs under the guard runner:
`tools/run.sh CAP_COREH TIMEOUT_S node tools/difftool/dist/cli.js …`.

### OLD / NEW

| form | meaning |
|---|---|
| `path/to/file.ts` | that file and every file it reaches through relative imports |
| `path/to/dir` | every `.ts`/`.tsx` file under the directory (not `node_modules`, `dist`, `build`, `lib`, dot-dirs), plus files they import relatively |
| `git:REV:path` | the same, read with `git show`/`git ls-tree` from the repository given by `--repo` (default: the working directory); read-only |

Functions are paired by `key` = `module::qualifiedName`: `module` is the path relative to the
spec's root (for two single-file specs it is `<file>`, so `old.ts` pairs with `new.ts`);
`qualifiedName` is `f` (function declaration or `const f = (…) => …`), `C.m` (method or static
method) or `C.constructor`. A function is *changed* when its printed text without comments
differs.

### Options

| option | default | effect |
|---|---|---|
| `--json FILE` | none | write the result (schema below) to FILE; `--json -` writes it to stdout and the table to stderr |
| `--repo DIR` | cwd | repository for `git:` specs |
| `--work DIR` | `scratch/difftool/diff-<time>-<pid>` | scratch directory (slices, Lean files); proof files live here |
| `--runs N` | 1500 | fuzzing runs per changed function (fewer when the input space is small or after 60 s) |
| `--seed N` | 1 | seed of input generation (same code + seed = same inputs) |
| `--timeout-ms N` | 1000 | per-call timeout in the Node sandbox |
| `--no-lean` | Lean on | skip translation, Lean confirmation and proofs |
| `--tactic FILE` | built-in | proof script of the statement over all worlds |
| `--tactic-wf FILE` | built-in | proof script of the statements over worlds with allocated argument arrays (`_wf`, `_wfs`, `_wfo`; the observational statement `_obs` always uses its built-in script) |
| `--heartbeats N` | 400000 | `maxHeartbeats` per theorem |
| `--lean-timeout S` | 400 | seconds per Lean process (a batch that times out or crashes is retried one function per process) |
| `--only REGEX` | all | only functions whose `key` matches |
| `--details`, `-q` | | human output only |

Script placeholders: `{OLDCALL}` `{NEWCALL}` (call lemmas), `{OLD}` `{NEW}` (namespaces), `{F}`
(base name), `{DESTRUCT}` (an `rcases` pattern for the arguments), `{DEFS}` (definitions and
non-recursive call lemmas). The theorem statements themselves are fixed (below).

### Exit status

| code | meaning |
|---|---|
| 0 | no changed function is REFUTED or REFUTED* |
| 1 | at least one changed function is REFUTED or REFUTED* |
| 2 | usage error or internal error (no result written) |

## Result (`strictts-diff/v1`)

```jsonc
{
  "schema": "strictts-diff/v1",
  "command": "diff",
  "old": "git:abc123:src", "new": "src",          // the specs as given
  "options": { "seed": 1, "runs": 1500, "lean": true, "tactic": "default", "tacticWf": "default" },
  "summary": { "changed": 6, "proved": 2, "refuted": 1, "refutedNodeOnly": 1, "unknown": 2, "added": 1, "removed": 1 },
  "functions": [ /* one entry per changed, added or removed function */ ]
}
```

Each function:

| field | type | meaning |
|---|---|---|
| `key`, `file`, `name` | string | see pairing above (`file` relative to the spec root) |
| `kind` | `function` \| `arrow` \| `method` \| `static` \| `ctor` | |
| `status` | `changed` \| `added` \| `removed` | added/removed functions get no verdict |
| `verdict` | `PROVED` \| `REFUTED` \| `REFUTED*` \| `UNKNOWN` \| `null` | `null` exactly when status is not `changed` |
| `reasonCodes` | string[] | why the verdict is UNKNOWN or REFUTED* (codes below); empty for PROVED and REFUTED |
| `reasons`, `notes` | string[] | human-readable explanations (wording not stable) |
| `counterexample` | object \| null | present for REFUTED and REFUTED* |
| `proof` | object \| null | present when a proof was attempted |
| `fuzz` | `{runs, inconclusive, ms}` \| null | null when fuzzing did not run |

### Verdicts

* **PROVED**: Lean checked `theorem equiv_<id>` (or `equiv_<id>_wf`, `equiv_<id>_wfs`, `equiv_<id>_wfo`, `equiv_<id>_obs`) in `proof.file`, and
  `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound` (plus `Lean.ofReduceBool`
  when `bv_decide` was used: `proof.nativeAxiom = true`). `proof.statement` says what was proved:
  * `all-worlds`: `∀ (vs : Vals TT args) (w : World TT), JS.exec (callFun I Old.program Old.fRef vs) w = JS.exec (callFun I New.program New.fRef vs) w`, for every `I : Impl`;
  * `allocated-arguments`: the same equation for explicit arguments, for every world in which
    each array, Map and Set argument is an allocated cell (`w.heap.get? (k, a) = some c`,
    `a < w.next`, arrays with fewer than 2^32 elements), which every state of a run satisfies;
  * `allocated-arguments-strlen` (additive value, 10-24): the allocated-arguments statement where,
    in addition, each string argument has at most 2^53 - 1 code units (`s.length < 2 ^ 53`, the
    maximum length of an ECMAScript String, ECMA-262 6.1.4; the model's strings have no bound).
    Attempted only for functions with string arguments, and reported only when neither of the
    statements above was proved. A consumer that does not know the value can count it as not
    proved;
  * `allocated-arguments-objects` (additive value, 10-24): the allocated-arguments statement where,
    in addition, each object argument (a class instance) is an allocated cell
    (`w.heap.get? (.obj C fields, a) = some …`, `a < w.next`) whose fields are all initialised, and
    each array-valued field is an allocated cell with fewer than 2^32 - 1 elements (room for one
    `push`: JavaScript arrays stay below 2^32 elements, and a `push` beyond throws). Attempted only
    for functions with object arguments of a known class, and reported only when none of the
    statements above was proved; a consumer that does not know the value can count it as not
    proved;
  * `observational` (additive value, 10-24): clearly WEAKER than the four statements above, which
    are equalities of whole worlds. `theorem equiv_<id>_obs`, for every world in which each
    array, Map and Set argument is an allocated cell (as in `allocated-arguments`) and each string
    argument has at most 2^53 - 1 code units (as in `allocated-arguments-strlen`):
    `Obs.Equiv (R w.next) (JS.exec (callFun I Old.program Old.fRef vs) w) (JS.exec (callFun I New.program New.fRef vs) w)`
    with the definitions of `StrictTS/Proof/Obs.lean` (copied, with their names, from equiv-lean's
    `EquivLean/Bridge/TS/Obs.lean`): both runs diverge, or both end and their outcomes are related
    by `R`. `R` is `Obs.ObsEq` when the result type holds no references (numbers, strings,
    booleans, errors, enums, `undefined`/`null`, and tuples, records, optionals and unions of
    these): the same completion (value, thrown error or panic) and `WorldObs w.next`. `R` is
    `Obs.ArrObs` when the result is an array of such values: `WorldObs w.next`, and the same error,
    or the same array below `w.next` (one the caller passed in), or two arrays the callee
    allocated (addresses `≥ w.next`, possibly different) with equal contents. `WorldObs n` compares
    the console output, every heap cell at an address below `n` (all the caller can hold a
    reference to), and how many answers of `Math.random()`, `Date.now()` and external calls were
    consumed. NOT compared: the cells the callee allocated (other than a returned array, through
    `ArrObs`), the allocation counter `next`, and the asynchronous state (job queue, timers,
    unhandled rejections). The statement is therefore attempted only when neither translation
    contains a construct that schedules asynchronous work (promises, `async`/`await`,
    `queueMicrotask`, `setTimeout`, asynchronous externals), and only when no equality statement
    was proved (a second Lean pass); functions with other result types (arrays of references,
    maps, sets, objects, functions) get no observational statement. A consumer that needs equality
    of worlds, or that does not know the value, counts it as not proved.
  * `old-no-panic` (additive value, 10-27): WEAKER than equality of worlds, reported only when none
    of the statements above was proved (second Lean pass). Since master 10-27 ~09:10Z the function's
    `verdict` is then UNKNOWN (with this `proof` attached and a reason saying so), never PROVED; the
    first run that used it (R6d, master 25790c3) reported verdict PROVED with this statement. `theorem equiv_<id>_np`, for every
    argument list `vs` and world `w`: `JS.exec (callFun I Old.program Old.fRef vs) w =
    JS.exec (callFun I New.program New.fRef vs) w ∨ ∃ s w', JS.exec (callFun I Old.program Old.fRef vs) w =
    some (.error (.panic s), w')`: the two runs are equal, or the old run panics (a read that the
    TypeScript types exclude, a non-null assertion on undefined, or another designed panic), where
    the new version may do anything. It covers changes that keep every run of the old version that
    stays within its types and only replace a designed panic (e.g. a return type widened from `T`
    to `T | undefined`, so that an out-of-bounds read becomes `undefined`). A consumer that needs
    equality, or that does not know the value, counts it as not proved.
  Equality of worlds includes heap, console output, job queue, timers and the allocation counter.
  The statement is attempted only when the translated module state (globals and their
  initialisers) is identical in both versions.
* **REFUTED**: a concrete call on which old and new behave differently in Node (outcome, console
  output, unhandled rejections, or the arguments/receiver afterwards), reproduced in fresh
  processes, and confirmed by running both translated functions on the same call under the Lean
  semantics (Lean's output equals Node's for each version and differs between them).
* **REFUTED\***: the same Node counterexample without the Lean confirmation (the function or its
  driver is outside the StrictTS subset, or Lean disagreed with Node: code
  `node-only:lean-mismatch`, which is a translator/semantics bug report).
* **UNKNOWN**: neither; `reasonCodes` says why.

A Node counterexample always takes precedence: no proof is attempted for a refuted function.
Runs that time out, overflow the stack, crash, or read a host global the sandbox does not provide
(`process`, `fetch`, …) never count as differences. Inputs are values of the old parameter types
that the new parameter types also accept (otherwise `signature-changed`).

### Counterexample

| field | meaning |
|---|---|
| `call` | the call as TypeScript, e.g. `magnitude(-0)`, `new Cart(1).add(2)` |
| `inputs`, `receiverArgs` | the arguments (and the receiver's constructor arguments) as tagged values |
| `old`, `new` | observations: `outcome` (`return V`, `throw Name: message`, `resolve V`, `reject Name: message`, `pending`), `console` (lines), `args` (arguments after the call), `receiver` (after the call, or null), `unhandled` (rejections) |
| `differs` | which of `outcome`, `console`, `arguments after the call`, `receiver after the call`, `unhandled rejections` differ |
| `leanConfirmed` | true exactly for REFUTED |
| `lean` | `{old, new}`: the confirmation driver's output under Lean, or null |

Values in observations are printed canonically: numbers as JavaScript prints them except `-0`;
`NaN` equals `NaN`; strings JSON-quoted (lone surrogates as `\udXXX`); bigints with `n`; arrays
`[…]`, Maps `Map{k => v}`, Sets `Set{…}`, class instances `C{…}` with sorted fields, plain objects
`{…}` with sorted keys and without undefined-valued keys; arrays, Maps, Sets and instances that
occur twice are labelled `#1=…` and referenced as `#1`; functions as `<function>`.

Tagged values (`inputs`): `{"t":"n","v":1.5}` (numbers; `v` is `"NaN"`, `"Inf"`, `"-Inf"`, `"-0"`
for the special values), `{"t":"s","v":"…"}`, `{"t":"b","v":"123"}` (bigint), `{"t":"B","v":true}`,
`{"t":"u"}` (undefined), `{"t":"z"}` (null), `{"t":"a","v":[…]}` (array or tuple),
`{"t":"o","v":[["key",…],…]}` (object, keys in order), `{"t":"m","v":[[k,v],…]}` (Map),
`{"t":"S","v":[…]}` (Set), `{"t":"c","cls":"C","args":[…]}` (`new C(…)`),
`{"t":"ta","kind":"Uint8Array","v":[…]}`, `{"t":"d","v":ms}` (Date), `{"t":"p","v":…}`
(`Promise.resolve(…)`).

### Proof

| field | meaning |
|---|---|
| `file`, `theorem` | the Lean file (in the work directory) and the theorem name (`equiv_<id>`, `equiv_<id>_wf`, `equiv_<id>_wfs`, `equiv_<id>_wfo`, `equiv_<id>_obs` or `equiv_<id>_np`; the observational and old-no-panic statements are in files `obs_NN.lean`); the file is checked by `lean` with the repository's `LEAN_PATH` |
| `statement` | `all-worlds`, `allocated-arguments`, `allocated-arguments-strlen`, `allocated-arguments-objects`, `observational` or `old-no-panic` (see Verdicts; `observational` and `old-no-panic` are weaker than equality of worlds) |
| `checked` | the theorem was accepted (true exactly for PROVED) |
| `axioms` | the output of `#print axioms` (a failed attempt contains `sorryAx`) |
| `axiomsOk` | no `sorryAx`, only the standard axioms and possibly the native-code axiom |
| `nativeAxiom` | `Lean.ofReduceBool` or `Lean.trustCompiler` used (`bv_decide`) |

### Reason codes

| code | meaning |
|---|---|
| `outside-subset` | the translator rejects old or new (StrictTS subset rules or TypeScript errors in the slice) |
| `external-module` | the function needs a package or a non-TypeScript module (no slice, no run) |
| `signature-changed` | parameter types, optionality or the receiver's constructor changed incompatibly |
| `kind-changed` | e.g. a function became a method |
| `inputs-not-generated` | a parameter type has no input generator (functions, RegExp, …) |
| `fuzz-error` | the sandbox could not run the slice (e.g. a host global used while loading) |
| `slice-error` | the function could not be sliced or described |
| `module-state-differs` | module variables or their initialisers differ, so no world-equality statement |
| `translated-signatures-differ` | the translated types differ (e.g. a widened string-literal union) |
| `target-not-translated` | the function has no translation (e.g. an uninstantiated generic) |
| `no-counterexample` | fuzzing ran without finding a difference |
| `no-proof` | a proof was attempted and failed; refined by `proof:loops`, `proof:callbacks`, `proof:map`, `proof:async`, `proof:call` (recursion), `proof:allocation`, `proof:strings`, `proof:numbers`, `proof:timeout`, `proof:other` (shape of the residual goal) |
| `lean-disabled`, `lean-error` | Lean stage off, or a Lean-side failure before the proof |
| `soundness-alert` | a proof checked although fuzzing found a difference (never expected; report it) |
| `node-only:driver-outside-subset` | REFUTED*: the confirmation driver is outside the subset |
| `node-only:lean-mismatch` | REFUTED*: Lean's output differs from Node's on the driver (translator/semantics bug) |
| `node-only:not-observable` | REFUTED*: the driver does not print the differing part (identity, private state) |
| `node-only:lean-failed`, `node-only:lean-disabled` | REFUTED*: Lean did not run or failed |
| `other` | anything else |

## Stability guarantees

Frozen for `strictts-diff/v1`:
* the invocation, the spec forms, the options above and their defaults, the exit codes;
* the result's field names, types and nesting, the verdict and status values, the reason-code
  set, the `statement` values (to which `allocated-arguments-strlen`,
  `allocated-arguments-objects` and `observational` were added on 10-24, additive changes within
  v1), the canonical
  printing and the tagged-value encoding;
* the verdict semantics and the two theorem statements;
* `strictts-diff selftest` (fixture `test/fixture`, expected projection `test/fixture/expected.json`)
  passes; it validates the result with the same constraints as the JSON Schema. The projection is
  fixed; the fixture's function bodies may change so that it keeps one function per outcome as
  later versions prove or confirm more (10-24: `limitOf`, `total`, `anyNegative`, which had become
  REFUTED, all-worlds and PROVED).

Not part of the interface: the wording of `reasons`, `notes` and the table; the layout of the
work directory and the Lean files beyond `proof.file`/`proof.theorem`; the proof scripts' tactics
(a proof found today stays a valid proof, but later versions may prove more); the subcommands
`bench`, `validate`, `history` (maintenance tools). Any change to a frozen item produces
`strictts-diff/v2`.
