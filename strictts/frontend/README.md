# StrictTS frontend: TypeScript → Lean 4 IR

`frontend/` translates a TypeScript program (files or a `tsconfig.json` project) into Lean 4
definitions of the StrictTS IR (`StrictTS/Core/Syntax.lean`), after checking that the program
is in the StrictTS subset (`DESIGN.md` §2). The generated file can be run by the Lean
interpreter of the semantics (`StrictTS.runOutput`) and is the starting point of proofs.

## Build and run

```sh
cd frontend && npm install && npm run build      # typescript@5.9.3, compiles src/ to dist/
node frontend/dist/cli.js prog.ts -o Prog.lean   # translate (exit 1 + diagnostics if not in the subset)
node frontend/dist/cli.js -p tsconfig.json -o Prog.lean
node frontend/dist/cli.js --check prog.ts        # subset check only
node frontend/dist/cli.js --eval prog.ts -o Prog.lean && lake env lean Prog.lean   # run it
node frontend/dist/cli.js --modular OUTDIR --namespace NS prog.ts   # one module per function (below)
```

Options: `--namespace N` (default `Prog_<file>`), `--eval` (append `#eval runMain …`, which
prints the console output and `[ok]` / `[uncaught Name: message]` / `[PANIC …]`),
`--abbrev-types` (name large repeated types), `--strict` / `--no-dyn` (the original subset:
`unknown` and `any` are rejected, no `dyn` values; also in coverage mode). Diagnostics have the form
`file:line:col [rule-id] message`.

## Output

```lean
namespace Prog_x
def TT : TypeTable                       -- named recursive types and classes (fields)
def fooRef : FunRef tys[...] ret := ⟨i, "foo"⟩   -- one per function (methods: C_m, constructors: C_new)
def g_x : GRef ty := ⟨i, "x"⟩            -- module-level variables (heap cells 0..n-1)
def fooDef : FunDef TT where ...         -- the IR of each function
def mainBlock : Block TT [] .undef       -- module bodies, in import order
def program : Program TT
theorem foo_call (I : Impl) (vs : Vals TT [...]) :
    callFun I program fooRef vs = applyLam I program fooDef.lam .nil vs
abbrev «pkg:getDoc_ext» : ExtFun := ⟨"pkg:getDoc", [...], ret⟩   -- one per external function called
```

A program that calls external functions also imports `StrictTS.Proof.Extern`; its `ExtFun`
abbreviations have the exact names and signatures of the `extern` nodes, so that specs can state
oracle answers (`w.answer «pkg:getDoc_ext» vs n = .ok v`).

The notations of `StrictTS/Frontend/Prelude.lean` (`tys[…]`, `args[…]`, `var! n`, `mem! n`,
`js! "…"`, …) are macros that expand to plain IR constructors.

### Modular output (incremental, cacheable proofs)

`--modular OUTDIR` (with `--namespace NS`, optionally `--index-map FILE.json`) writes a directory
of Lean modules instead of one file, so that a proof about a function depends only on that
function's IR and its callees' signatures, and its `.olean` survives edits elsewhere:

| Module | Contents | Imports |
|---|---|---|
| `OUTDIR/NS/Types.lean` | `TT` (abbrev) and the class field lists `«C».fields` | prelude |
| `NS/Refs/<f>.lean` | `def «fRef» : FunRef tys[...] ret := ⟨i, "f"⟩` | prelude |
| `NS/Globals/<g>.lean` | `def «g_x» : GRef ty := ⟨i, "x"⟩` (module-level variables) | prelude |
| `NS/Externs/<e>.lean` | `abbrev «pkg:getDoc_ext» : ExtFun := ⟨"pkg:getDoc", [...], ret⟩`, one per signature of an external function (the single-file names) | prelude, `StrictTS.Proof.Extern` |
| `NS/Defs/<f>.lean` | `def «fDef» : FunDef TT` and the call rule over any program that contains it: `theorem «f_call_of» (I) (P : Program TT) (hf : P.funs[«fRef».idx]? = some «fDef») (vs) : callFun I P «fRef» vs = applyLam I P «fDef».lam .nil vs` | `Types`, `StrictTS.Proof.CallRule`, the `Refs`, `Globals` and `Externs` its IR mentions |
| `NS/Program.lean` | `mainBlock`, `program`, `theorem «f_lookup» : program.funs[«fRef».idx]? = some «fDef»` and the usual `«f_call»` | `Types`, every `Defs`, `Globals` and `Externs` module |

Indices are stable. The index map (default `OUTDIR/NS/index.json`; read if present, then
rewritten) lists the functions and module-level variables by Lean name, in index order, with
their module names, and the external signatures with their abbreviations (numbered per external
name in order of first appearance, so a fresh map gives the single-file names, and kept
afterwards). Existing names keep their index and module, new names are appended, and the
slot of a removed function holds `«removed function»`, whose calls panic; a removed name stays
in the map (`"removed": true`) and gets its slot back if it returns. A file is written only when
its text changes, and the generated `Refs`/`Defs`/`Globals`/`Externs` modules of removed names are deleted
(only files that start with the generated header). Lake therefore rebuilds:

* a function's body edited: its `Defs` module and `Program` (and whatever imports `Program`);
* a function added or removed: its own modules and `Program`;
* a function's signature changed: also the `Defs` of its callers;
* a type or class changed: everything (`Types`).

The lookup facts are linear in the number of functions: `program.funs` is defined by its
suffixes (`funs_k := «d_k» :: funs_(k+1)`) and each `funs_drop_k : program.funs.drop k = funs_k`
follows from the previous one, since `rfl` on `program.funs[i]?` walks the list (73 ms per
function at 1000 functions, against 11 ms).

Proofs import only the `Defs` modules they are about and take the lookups as hypotheses; a
separate file instantiates them for `program` with the `_lookup` facts
([`examples/Modular`](../examples/Modular), library `Modular` in `lakefile.toml`):

```lean
import LoopsMod.Defs.maxOf
import LoopsMod.Defs.maxOfReduce
import StrictTS.Proof.Summarize

theorem maxOf_eq_maxOfReduce_of (I : Impl) (P : Program TT)
    (hf : P.funs[maxOfRef.idx]? = some maxOfDef) (hg : P.funs[maxOfReduceRef.idx]? = some maxOfReduceDef)
    (a : Nat) (xs : Array (Val TT .num)) (w : World TT) (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I P maxOfRef (.cons (.arr a) .nil)) w =
      exec (callFun I P maxOfReduceRef (.cons (.arr a) .nil)) w := by
  rw [maxOf_call_of I P hf, maxOfReduce_call_of I P hg]
  simp only [maxOfDef, maxOfReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

-- LoopsModProgram.lean (imports LoopsMod.Program):
theorem maxOf_eq_maxOfReduce … := maxOf_eq_maxOfReduce_of I program maxOf_lookup maxOfReduce_lookup a xs w hw
```

On `examples/Summarize/loops.ts` (17 functions, 36 modules), editing the body of `range` and
re-translating with the same index map rebuilds `LoopsMod.Defs.range`, `LoopsMod.Program` and
`LoopsModProgram`; adding a function builds its two modules and rebuilds `Program` and
`LoopsModProgram`; removing `range` rebuilds those two only. `LoopsModProof` and the other
`Defs` are never rebuilt. A `Refs` or `Defs` module takes 0.2 to 0.5 s to build, 0.2 s of it loading
the prelude. On the 88 programs of the corpus, the modular `program` prints exactly what the
single-file one prints.

## Truthiness, dictionaries and external calls

* Conditions, `!`, `&&` and `||` on non-booleans become explicit tests: a string `s !== ""`, a
  number `n !== 0 && n === n`, a bigint `n !== 0n`, `undefined` / `null` false, objects true,
  `opt` and unions by case analysis.
* An object type with one string index signature (`{ [k: string]: T }`, `Record<string, T>`),
  alone or with named properties whose types fit it (`{ v?: unknown; [k: string]: unknown }`), is
  a dictionary `.dict T`. A named property is an entry read at the type TypeScript gives it (a
  checked cast, a panic on a value of another type, where that is narrower than `T`: corpus
  `dict_named_props`); references share the dictionary, and it is not copied into a record type
  (a later write through it would not show; reject test `dict_named_to_record`). `o[k]` / `o.p`
  is `dictGet` (`opt T`), unwrapped
  where TypeScript types the read as `T` (a panic for a missing key, as for array indices) unless
  the program tests for a missing key (`?.`, `??`, `=== undefined`, or a truthiness test: `!`,
  conditions of `if` / `while` / `for` / `? :`, the left of `&&` / `||`; also for array
  elements, also past the end in loop conditions; corpus `dict_truthiness`, `past_end_loops`;
  `Object.prototype` names keep panicking); `o[k] = v` (also `op=`,
  `??=`, `++`) is `dictSet`, `k in o` `dictHas`, `delete o[k]` `dictDelete`, `Object.hasOwn` /
  `hasOwnProperty` `dictHasOwn`, `Object.keys/values/entries` the matching builtins; an object
  literal typed as a dictionary is `dictNew` followed by one `dictSet` per property (a spread of a
  dictionary copies its entries in order). Keys are strings, numbers (canonical string) or
  string-literal unions.
* `const a = new Array(n)` (or `Array(n)`, `n` a number) in a function, with `a` used in no
  nested function: JavaScript creates `n` holes. The array starts empty and grows by element
  writes `a[i] = v` (`arrSet`: a write past the end panics, since it would leave a hole); every
  other use of `a` (a read, `a.length`, a call, `return a`) first checks that its length reached
  `n` and panics otherwise, so a run that does not panic never observes a hole. A length that is
  not an integer in [0, 2^32 - 1] throws JavaScript's RangeError. Corpus `arrays_new_length`,
  `arrays_new_length_holes`; reject test `new_array_closure` (`new Array(n).fill(x)` is
  `arrMakeFill`).
* `Iterator<T, TReturn, TNext>` is the record of its methods: `next` (called without the TNext
  argument), optional `return` and `throw` (called without the error), each returning
  `IteratorResult<T, TReturn>`, the union of `{ done?: false, value: T }` and
  `{ done: true, value: TReturn }`; `it.next()` and `it.return?.()` call through the fields. The
  methods are closures: `this` in an object literal method is rejected, so no receiver is
  needed. In the strict subset the default TReturn (`any`) is `undefined`, which no program can
  observe there (reading it at type `any` is rejected; an `Iterator<T, X>` is then not converted
  to `Iterator<T>`). IteratorObject (the Iterator.prototype
  helpers), iterable iterators (`Symbol.iterator`), Map / Set / Array iterators and generators
  stay unsupported (corpus `iterator_records`; reject tests `iterator_this`,
  `iterator_return_any`).
* A call of a function or method declared outside the program and the modelled library
  (packages, host APIs) is `.extern "<module>:<Parent.name>" args`, typed by the checker's
  resolved signature; a method's receiver is the first argument, a `Promise<T>` result makes it
  `.externAsync` with `t = T`, and an `any` result takes the asserted or declared type
  (`JSON.parse(s) as T`). Property reads and writes on external objects are externs
  `"<Type>.get:<prop>"` / `"<Type>.set:<prop>"`; values of external types are `.ext "<module>:<Type>"`.
  Callbacks passed to external functions are rejected (`extern-callback`).
* A regular expression used as the receiver of `test` / `exec` or the pattern of `match` /
  `replace` / `replaceAll` / `split` / `search` becomes an extern whose arguments are the
  receiver, the pattern and the flags (flags in canonical order), then the other arguments:
  `re.test(s)` → `.extern "RegExp.test" [pattern, flags, s]`. A literal (at the call, or bound by
  `const`) gives them as string literals; any other regex is a value, the record of its `flags`
  and `source`: a literal used as a value, or `new RegExp(p, f)` / `RegExp(p, f)`, the extern
  `"RegExp.new"`, which throws Node's SyntaxError for a bad pattern or flags (the source escapes
  `/` as Node's does). `re.global` and the other flag properties are read from the flags. Match
  results are `.ext "RegExpExecArray"` / `.ext "RegExpMatchArray"`; an element read as `string`
  is unwrapped (a capture group that did not participate is `undefined`), and so is a group that
  `split` with a value puts into its result (a panic where it did not participate). `test` /
  `exec` (and `match` / `replace` without `g`) read and write `lastIndex` on a global or sticky
  regex: rejected on a literal bound to a name, a checked panic on a value with such flags
  (corpus `regex_values`, `regex_value_flags`). `lastIndex`, `===` on regex values, and replacer
  functions with a regex value (whose groups are not known) are rejected.
* `console.log` (also `console.info` / `console.debug`, which write to standard output too) of
  one string is the world's output; `console.warn` / `console.error` write to standard error,
  outside the modelled output, and are externs with no result (corpus `console_streams`).
* `Date.now()` is the world's `now` oracle; `Math.random()` its `random` oracle; `Date.now` and
  `Math.random` as values (a default `rand = Math.random`) are functions that call them. A timer
  handle typed by Node as `NodeJS.Timeout` (an object in Node) is a record holding the number
  the semantics' `setTimeout` returns: it can be stored, passed, compared with `null` /
  `undefined` and tested for truthiness (an object: always true; the number is at least 1 too),
  and `typeof` is "object" as in Node, while strings, numbers, arithmetic, other comparisons,
  methods (`unref`) and unknown values of it (where Node's `Symbol.toPrimitive` id would show)
  are rejected (`timer-handle`; reject tests
  `timer_*`, which declare the type in an ambient namespace: such namespaces holding only types
  are accepted). `String.fromCodePoint` checks each code point (Node's
  RangeError otherwise) and gives one or two UTF-16 code units; `m.keys().next().value` (also
  `values()` / `entries()`, and of a Set) is the first element in insertion order or undefined.
  A function value used where fewer arguments are passed gets `undefined` for a missing
  parameter of type unknown (`new Promise((r) => setTimeout(r, ms))`). Corpus `small_levers`.
  `String.raw` as a tag is the template's raw text (escape sequences as written, line breaks as
  LF) with the substitutions converted as in a template literal, e.g. the pattern of
  `` new RegExp(String.raw`^\d+$`) `` (corpus `string_raw`); other tags are rejected.
* `Promise.all` over a tuple of different types (TypeScript's tuple result, e.g.
  `const [doc, n] = await Promise.all([getDoc(r), count()])`), and over the empty tuple, is
  `promAllTup ts` on the tuple of promises (plain values as resolved promises, as for arrays):
  one reaction per element, registered in order, each storing its value into a box of the
  element's type; the result resolves when every box is filled (the empty tuple at once) and
  rejects at the first rejection, with the jobs Node runs. `Promise.allSettled` over an array
  (`promAllSettled t`) or a tuple (`promAllSettledTup ts`) gives `PromiseSettledResult<T>`
  records, `{ reason: unknown; status: string } | { status: string; value: T }` (`Ty.settled`),
  and never rejects; `reason` is `any` in TypeScript, so allSettled is not in `--strict`
  (reject test `all_settled_strict`). Corpus `async_all_tuple`, `async_all_tuple_reject`,
  `async_all_settled`.
* `unknown` and `any` are `.dyn`: `Val.dyn t v`, a value with its runtime type (no copy, so
  references keep their identity; StrictTS/Lib/Dyn.lean, the `dyn*` builtins in Sem.lean). An
  upcast is `toDyn t`; a downcast (TypeScript's narrowing, `as`, an `any` value in a typed
  position) is `unwrap (dynCast t x)`, a panic if the runtime value is not of type `t` (casts
  accept the same type, string ↔ string-literal union, `undefined` at `opt`, a union member;
  not yet record projection or JSON objects to records). A narrowing without IR type
  (`object`, `object & Record<"k", unknown>`, `any[]`) keeps the value as `dyn`. `typeof`,
  `instanceof Error`, `in`, `===` (also with `null` / `undefined`), truthiness, `String(x)`,
  template holes, `"…" + x`, `Array.isArray` and property and index reads (`dynGet`: own keys,
  `length` and indices, `message` / `name` of errors, a TypeError on `null` / `undefined`;
  prototype methods and properties of external objects panic) work on the runtime value, and
  so do `<`, `<=`, `>`, `>=` (ToPrimitive, an object giving its String(x); two strings by code
  units, other primitives by ToNumber; a bigint or function operand panics: corpus
  `dyn_compare`, `dyn_compare_bigint`).
  Other operations on such values (arithmetic, calls and method calls, writes, iteration,
  spreads, destructuring) are rejected as `any-op`. An untyped `JSON.parse` answers `dyn`
  (`EVal.dyn`, with `arr dyn` and `dict dyn` cells). `Number(x)` is ToNumber by runtime type
  (strings and objects through their string); `throw x` requires an Error (a checked cast);
  `for (const x of u)` iterates an array of any element type by index (`dynGet`, the length
  read at every step; other runtime values panic); array methods on a value narrowed to
  `any[]` act on it as `unknown[]` (a checked cast: JSON arrays, arrays created as
  `unknown[]`; arrays of another element type panic). A dictionary spread into a record
  literal provides a field when it has the key (`dictHasOwn`, decided at run time).
  `--strict` / `--no-dyn` turns all of this off (the original subset).

### Functions and records compared by identity

JavaScript functions and objects have identity: listener sets (`Set<() => void>`), maps keyed by
functions or objects, `===` between two functions or objects, and `indexOf` / `includes` /
`lastIndexOf` over arrays of them compare by identity, while StrictTS closures and records are
values. A function or record type whose values are compared like that anywhere in the program
(`src/identity.ts`, by its IR type) is translated everywhere as `box (fn …)` / `box (record …)`,
a heap cell holding the closure or the record. `box` is compared by address, so `Set`/`Map`
(SameValueZero) and `===` behave like JavaScript. Comparing with `undefined`, `null` or a
primitive value compares no objects, so only comparisons between two possible objects count: a
first version also counted `x === undefined` and `x === null`, which made most record types with
an optional use cells (and every value of a wider record type flowing into them a rejection), and
lost as many functions as it gained. A value whose type mixes records or tuples with primitives
compared with a primitive (`p === "none"` for `Item | "none"`) is a test of its members.
Recursive (named) record types stay values. Cells are created where JavaScript creates the
object: an arrow or function expression and an object literal (spreads included) at each
evaluation (`boxNew`), the rest of an object pattern, a top-level function or module-level const
arrow used as a value once at module start (a module variable), a nested function declaration
once per scope instantiation (at its declaration), a resolve function received from the library
once per call, and the value of an external call cast to such a record type (`JSON.parse(s) as
T`: nothing else holds it). Calls, field reads, method calls and destructuring through a cell read
it first (`boxGet`); so do conversions to plain functions and records (library callbacks, records
of a narrower type, unknown values) and calls of external functions, which receive the records
also inside arrays, optional values, unions and records (`JSON.stringify(items)`). A value
becoming a cell somewhere else would be a second object for one JavaScript object: a function of
another type, a record of a wider type, an unknown value, the result of an external function
(which may be an object the program holds, as `Object.values(o)` is). These are rejected
(`fn-identity`, `record-identity`); cells are never written. Corpus: `fn_identity_listeners`,
`fn_identity_keys`, `fn_identity_nested`, `record_identity`, `record_identity_json`
(subscribe/unsubscribe, two evaluations of one arrow, one declared function referenced twice,
insertion order, re-adding, `Map` keys and values, `===`, `indexOf`, resolvers kept in a `Set`,
nested functions per call, optional handlers and fields, spreads and rest patterns as new
objects, method calls through function fields, a discriminated union, objects given to and
parsed by `JSON`); rejections `record_identity_width`, `record_identity_unknown`, `tuple_eq`.
On snapshots of another project+a second project (another-project@5932a72, second-project@3574718; aggregates only),
function identity takes `map-key` from 234 to 34 functions (dyn) and from 143 to 3 (strict),
covered functions from 4609 to 4746 (dyn) and from 3001 to 3051 (strict), none lost; record
identity and the member tests then take `no-record-eq` from 26 to 5 (dyn) and from 17 to 0
(strict), covered functions to 4765 (dyn) and 3058 (strict). Two functions are lost in each mode,
both rejected external results: `localStorage` (its type holds a function cell) and
`Object.values` of an object holding records compared by identity. The remaining `map-key`
cases are `Map`/`Set` keys of type unknown, the remaining `no-record-eq` ones `includes` on
arrays of unknown values.

### Values of type unknown/any: state and next steps

Done (corpus programs `dyn_*`, `dict_spread_record`, each checked against Node): the `Ty.dyn`
semantics (StrictTS/Lib/Dyn.lean, `dynGet` / `dynHas` / `dynToStr` in Sem.lean, `EVal.dyn` /
`EVal.dict`), the translation of `unknown` and `any` with checked casts, the operations above,
and the `any-op` rule for the rest. External types that are only a string index signature
(Firestore's `DocumentData`) are dictionaries; a dictionary of unknown values (a parsed JSON
object, `DocumentData`) cast to a record type is converted field by field (`dictToRecord` in
core.ts: each field read by name and cast, absent optional fields `undefined`, nested records
recursively; an unknown value holding a record value is cast as itself).

Library levers done after that (corpus `levers_callbacks`, `extern_normalize`): `Boolean` as a
callback (`xs.filter(Boolean)`: truthiness of the first argument), `filter` with a type-guard
callback that narrows the elements (filter, then convert each kept element; the filtered array
is fresh, so the conversion is not observable, and a wrong guard panics), `Number(x)` of
optional values and unions, `push(...xs)` (all arguments first, a spread as a snapshot, then the
pushes in order), `s.normalize(form)` as the extern `"String.normalize"`, `Math.max/min(...xs)`
(a fold over the arguments, arrays through `arrReduce`), `s.matchAll(re)` as the extern
`"String.matchAll"` answering the array of match results (for `for…of`, spreads, `Array.from`).
Object literal spreads (corpus `object_spread_cond`): `...(c ? { k: v } : {})` and
`...(c && { k: v })` as optional spreads (the empty object contributes nothing), spreads of
optional values and unions of records (a case split: a field comes from the spread when its
runtime member has it), spreads of class instances and mutable objects (their fields read at
the spread), and spreads into mutable objects. A narrowing `as` (`x as string` for
`string | undefined`, a string to a literal union, a union to a member) is a checked narrowing
(panics on a mismatch; corpus `as_narrowing`; the strict subset keeps `as-downcast`).
`object` is an unknown value and `{}` the record without fields (corpus `object_types`; both
rejected in the strict subset), except where TypeScript narrows an unknown value to `{}` or
`{} | null` (`x !== undefined && x !== null`), which still holds strings and numbers: the value
stays unknown (corpus `dyn_eq_props`). `String(x)` of an unknown value holding an object with its own
`toString` / `valueOf` panics (records, dictionaries: Sem.lean `dynStr`), and instances of
classes with such methods cannot become unknown values (`unsupported-conversion`).
A computed read `o[k]` of a record or mutable object with a key of a string-literal union whose
cases are all properties (`labels[lang]`, `keyof typeof X`) is a case split on the key (corpus
`computed_keys`). `x instanceof C` with a library or package class (`Date`, typed arrays, a
Firestore `Timestamp`) is decided on the value's type, which is nominal for these (unknown
values: on the runtime type; corpus `instanceof_lib`). `s.replace(re, f)` / `replaceAll` with
a replacer function follows RegExp.prototype[@@replace]: the matches first (`String.matchAll`
for a global regex, `RegExp.exec` otherwise), then per match its index, match and groups
(extern reads), the replacer, and the pieces between matches (corpus `extern_regex`; the
difftest harness performs the same steps so that the replay matches; named groups rejected).

Coverage of the ten projects (functions): strict subset 39.1% → with unknown 52.7% → with any
54.5% → with the dyn operations 55.6% → with the library levers 58.5% → with spreads and
checked narrowings 61.4% → with `object` / `{}` 61.9% → with computed keys 62.7% → with library
instanceof and replacer functions 63.4% (LOC 17.0% → 32.2%); the strict subset
alone is now at 41.5% (spreads and library levers count there too); `any-op` blocks 17
functions (9 as the only rule).

Next, by number of functions blocked (listener sets, formerly first, are done: functions
compared by identity above):
1. `Map<unknown, …>` keys (22 functions, rule `map-key`): needs SameValueZero on runtime values
   (`Ty.keyable .dyn` and a `dyn` case of `Conv.svz` in Core; `Ty.eqable` must stay false so
   that `seq` is unchanged).
2. Records with typed arrays, sets or maps cast from dictionaries of unknown values (rejected as
   `unsupported-conversion`: the conversion would copy them, which changes aliasing; either a
   documented copy for fresh JSON values or a typed EVal answer at the extern).
3. `typeof` and `in` on strings, Maps and Sets held as unknown; `for…of` over them (strings
   iterate code points); `x.method()` on unknown values other than arrays.
4. Other library gaps by count (`unsupported-builtin`): typed array `subarray` / `set` (19).

## Differential testing

```sh
tools/run.sh 0.4 590 node tests/difftest/run.js [--only REGEX] [--details]
```

runs every program of `tests/corpus` on Node and on the Lean semantics and compares the
output line by line (see the header of `tests/difftest/run.js` for the `@numbers`, `@extern`,
`@skip`, `@gap`, `@panic` and `@reject` markers). For an `@extern` program the Node run records every
external call (name, arguments, result or error) and every `Date.now()` value
(`tests/difftest/harness.cjs`), and the Lean run answers its externs from that record
(`runMainTrace` in the prelude): a call whose name or primitive arguments differ throws
`TraceMismatch`. Generated Lean files are written to `tests/difftest/out/`.

## Coverage of real projects

```sh
node frontend/dist/cli.js --coverage -p tsconfig.json --report OUT.json [--only-dir DIR] [--label L]
tests/coverage/run_all.sh [SUFFIX]; python3 tests/coverage/analyze.py tests/coverage/*SUFFIX.json
```

translates every function, method, constructor and module-level arrow of a project on its own
(other project functions are assumed translatable; reasons found in one statement do not hide
later ones) and reports per function the rules that block it, the external functions it calls
and the LOC; the summary has covered/total functions and LOC, the top rules with the number
of functions they alone block, and the top externals. The project is only read (no emit).

`--emit-lean OUT.lean` also writes one Lean module with the IR of the covered functions
(`src/partial.ts`): they are translated normally, with the callees, classes and module
variables they need; a function whose body (or a callee's) fails is left out, as is a module
variable initialiser that fails (the variable is then uninitialised: reading it throws).
Module-level `const f = (…) => …` and arrows passed to module-level calls become functions.
Next to the module, `OUT.funs.json` lists the emitted functions with their declarations (file,
line, role, whether generic; `tools/validate` drives them). A covered generic function (or
arrow), which has no call site there to fix its type arguments, is emitted at one instance
(unless `--no-emit-generics`): the definition a call site with those type arguments makes
(each type parameter := number; `extends PropertyKey` /
`extends string` := string, `extends number` := number, as `tools/public/mono.js`; another
constraint: left out, with the reason among the failures that `STRICTTS_EMIT_FAILURES=1`
prints), named like `chunkBy_number`; its `OUT.funs.json` entry has the generic function's own
file, line, name and kind with `generic: true` and the instance (`"inst": {"T": "number"}`)
(difftest check `coverage/generics`: the instances equal the use-site definitions).
`tests/coverage/emit_all.sh` emits all ten projects into `tests/coverage/lean/`, and
`tests/coverage/elab.sh FILE…` elaborates modules with their times.

## Source layout

| file | role |
|---|---|
| `src/index.ts`, `src/cli.ts` | program construction (strict compiler options, host declarations `lib/strictts-env.d.ts`), entry points |
| `src/check.ts` | syntactic subset rules |
| `src/analysis.ts` | per-variable facts (reassigned? captured?), object types whose fields are assigned |
| `src/types.ts` | TypeScript types → `Ty` (records/objects/named recursive types, unions, enums, classes) |
| `src/core.ts` | translator state, bindings, conversions (coercions and narrowing), ANF helpers |
| `src/stmts.ts`, `src/exprs.ts`, `src/calls.ts`, `src/functions.ts` | lowering of statements, expressions, library and external calls, functions/classes/lambda lifting |
| `src/regex.ts`, `src/dict.ts` | regular expressions as externs and values; objects used as dictionaries |
| `src/coverage.ts`, `src/partial.ts` | per-function coverage mode; partial programs of the covered functions |
| `src/ir.ts`, `src/emit.ts` | named IR and its de Bruijn emission (captures, slot mutability, Lean text) |
| `src/modular.ts` | modular output: one module per function, stable indices (index map), incremental writes |
