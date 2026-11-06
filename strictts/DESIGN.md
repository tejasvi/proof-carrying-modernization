# StrictTS: design

StrictTS is a statically typed subset of TypeScript with a formal semantics in Lean 4,
designed so that proofs about real TypeScript code need as little manual work as possible.

## 1. Principles

1. **No dynamic-type branching in proofs.** The IR is intrinsically typed: `Expr TT Γ t` only
   contains well-typed terms, and `Val TT t` has exactly one constructor for every primitive `t`.
   Evaluation has no "type error" outcome, so no proof ever has a case for it.
2. **No implicit coercions.** Every conversion is an explicit IR node (`numToStr`, `strToNum`,
   template-literal pieces, …). `==`, truthiness of non-booleans and mixed-type operators are
   rejected by the translator; the one exception is the nullish test `x == null` / `x != undefined`,
   which coerces nothing (true exactly for null and undefined).
3. **Fixed object shapes.** No prototypes, no `delete`, no computed property names on records,
   no inheritance (v1). A method call is a direct call.
4. **Soundness gaps become proof obligations, never silent assumptions.** Where TypeScript's
   own type system is unsound (`a[i]` typed `T` but out of bounds, `x!`, holes, reading an
   uninitialised field), the semantics produces `panic`. A theorem about a program that does
   not panic therefore holds of the real JavaScript program.
5. **One standard monad.** `JS TT = ExceptT Exc (StateT (World TT) Option)`; the interpreter is
   a single `partial_fixpoint` definition (least fixpoint, `none` = divergence, no fuel). Program
   equivalence is equality of denotations, and `Std.Do`/`mvcgen`, `simp`, `grind`, `omega` and
   `bv_decide` work on the unfolded code.
6. **Implementation-defined behaviour is a parameter** (`Impl`: `Math.pow`, `Math.sin`, …,
   locale-dependent string functions) and nondeterminism is an oracle in the world
   (`Math.random`, `Date.now`, and every external library call: `Expr.extern` is answered by
   `World.ext`, indexed by the number of external calls made; external objects are opaque
   handles of type `Ty.ext name`).
7. **External answers have the types the program gives them (an assumption).** An external
   call is answered at its declared result type, and an `any`-typed answer that the program
   asserts with `as T` (`JSON.parse(text) as Settings`) or declares by an annotation is answered
   at `T`. The model trusts these claims, as it trusts library declarations in general: an
   input that violates the assertion is outside the model. Where ECMA-262 contradicts a
   declaration, the declaration is corrected instead of assumed: `JSON.stringify` answers
   `string | undefined`, and undefined where a string is needed is a §1.4 panic. (A
   checked-cast mode for answers at `unknown` is a possible later option.)

## 2. The subset

| Allowed | Rejected (rule) |
|---|---|
| `number`, `bigint`, `boolean`, `string`, `undefined`, `null`, `void` | `any`, `unknown` (except a `catch` variable used as `Error`), `object`, `{}`, `Function`, `symbol`, `never` values |
| objects used as dictionaries (`{ [k: string]: T }`, `Record<string, T>`): `o[k]`, `o[k] = v`, `k in o`, `delete o[k]`, `Object.hasOwn`, `Object.keys/values/entries`, in ECMA-262 key order | reading an inherited `Object.prototype` key (`o["toString"]`) or assigning `__proto__` (`panic`) |
| calls of external (library, host) functions and values of external types, typed by their declarations: oracle answers (`Expr.extern`, `Ty.ext`); `RegExp` and `JSON` are external for now | callbacks passed to external functions; external functions stored in arrays or maps |
| arrays `T[]`, `readonly T[]`, tuples (never mutated), `Map`, `Set`, typed arrays; `const a = new Array(n)` filled by writes at its end before any other use | sparse arrays / holes (runtime `panic`), `arguments` |
| interfaces / object types (records), classes without `extends` | prototype access/mutation, `__proto__`, `Object.setPrototypeOf`, `Object.defineProperty`, getters/setters with side effects on other objects |
| unions: `T \| undefined`, string-literal unions (enums), discriminated unions, disjoint primitive unions | `==` and `!=` other than against null or undefined, `in` and `delete` outside dictionaries, `for…in`, `with`, `eval`, `new Function`, labels on non-loops |
| closures (capturing `const` bindings; captured `let` bindings are boxed) | generators, `yield`, decorators, `Proxy`, `Reflect`, `Symbol` |
| `async`/`await`, `Promise` (resolve/reject/then/catch/finally/all/race/new) | `x + y` with mixed types, `as` downcasts |
| `try`/`catch`/`finally`, `throw new Error(…)` (also `TypeError`, `RangeError`, …) | throwing non-`Error` values |
| template literals with `string`/`number`/`bigint`/`boolean` holes (explicit conversions) | template holes of other types |
| generics (monomorphised by the translator) | higher-kinded tricks, conditional types at runtime |

Truthiness is desugared by the translator into explicit tests, so the IR never coerces: a string
`s` is tested as `s !== ""`, a number `n` as `n !== 0 && n === n` (NaN is falsy), a bigint as
`n !== 0n`, `T | undefined` / `T | null` as the presence test (followed by the test of `T` when
`T` is primitive), and `!x` likewise.

## 3. Types (`StrictTS/Core/Ty.lean`)

`num | bigint | bool | str | undef | null | err | arr t | tarr k | map k v | set t | tup ts |
record fs | obj c | named n | opt t | union ts | enum cases | fn args ret | promise t | box t`.

* Records are **values**: an object type none of whose fields is ever assigned anywhere in the
  program is a record. Width subtyping becomes an explicit projection (sound because records
  are immutable). A record or function type whose values are compared by identity somewhere
  in the program (`===` between two possible objects, not with `null` / `undefined` /
  primitives; `Set` elements, `Map` keys, `indexOf` / `includes`) is translated
  everywhere as `box t`: a cell created where JavaScript creates the object, compared by
  address (`frontend/src/identity.ts`); a value of a wider record type, an unknown value or an
  external result cannot become such a cell. `===` on other records and on tuples is rejected.
* Object types with an assigned field, and all classes, are **heap objects** (`obj c`), used
  nominally (no width subtyping). Object operations (`newObj c fs`, `getField`, `setField`)
  carry the class's field list `fs` explicitly, so no type of the IR mentions the type table
  and `simp` never has to reduce it; the heap key of an instance is `(.obj c fs, address)`.
* Recursive value types are `named n` with `TT.alias n` their definition.
* `opt t` is `t | undefined`; other unions are tagged with the member index.

## 4. The heap and the world (`StrictTS/Core/World.lean`)

The heap is an extensional dependent map keyed by `(HKind, address)`. Cells of different kinds
or element types never alias, so writing a `number[]` provably leaves every `string[]`, `Map`
and object unchanged (no side condition). The world also holds the console output, the
microtask queue, timers and the oracles.

## 5. Soundness by construction

`evalE : Expr TT Γ t → Env TT Γ → JS TT (Val TT t)` and
`evalB : Block TT Γ ρ → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)`: the Lean types of the
interpreter are the type-preservation theorem, and there is no stuck state. Every run ends in
one of: a value of the static type (`some (.ok v, w)`), a JavaScript exception
(`.error (.thrown e)`), a `panic` (`.error (.panic msg)`), or divergence (`none`). Panics are
produced only at the places listed in §1.4, where TypeScript's own typing is unsound and real
JavaScript would continue with `undefined` or a hole; a proof that a run returns
`some (.ok …)` therefore also proves that none of those happen.

## 6. Semantics (`StrictTS/Core/Sem.lean`)

* Expressions: `JS TT (Val TT t)`; they never change the environment.
* Statements/blocks: `JS TT (Completion TT ρ × Env TT Γ)` with ECMAScript completion records
  (`normal | brk n | cont n | ret v | retP p | exc e`); a thrown exception inside `try` keeps
  the assignments made before it.
* Loops iterate live (`for…of` re-reads the length; `Map` iteration sees insertions and skips
  tombstones), exactly as specified.
* `async` bodies run in continuation-passing style with first-order continuations (`AK`); await
  registers a reaction on the awaited promise; jobs implement ECMA-262 PromiseReactionJob and
  NewPromiseResolveThenableJob, so the interleaving of output matches Node.

## 7. Proof layer

See `StrictTS/Proof/*` and `README.md`: simp sets that unfold the interpreter on concrete IR,
loop rules (invariant and relational), the number bridge (`F64` ↔ `Int` for safe integers,
`F64` ↔ `BitVec 32` for int32 idioms), Array/Map model lemmas, and tactics for differential
equivalence and invariants.
