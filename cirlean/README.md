# cirlean: verifying C++ through ClangIR in Lean 4

cirlean is a formal semantics of the ClangIR (`cir`) MLIR dialect in Lean 4,
with native Lean models of C++ standard library idioms and tactics that turn a
C++ function into verification conditions automatically. Typical proofs are
3–5 lines.

The semantics works on CIR *as Clang emits it*, before any lowering:

* structured loops (`cir.for`, `cir.while`, `cir.do`) stay loops; the loop
  rule takes an invariant over the C++ variables;
* lexical scopes (`cir.scope`) and RAII cleanups (`cir.cleanup.scope`) stay
  scopes; destructors run on every exit (fall-through, `return`, `break`,
  `continue`, exceptions);
* classes stay classes: an object is one structured value (`agg` of its
  members), not bytes; pointers are a block plus a path of member/element
  steps. A scalar access through a pointer to an aggregate reaches the
  scalar the aggregate starts with, and a character access a byte of an
  object (a last path step `byte k`); pointer arithmetic and bytes are
  described under Semantics. In a C++ module (`cir.lang<cxx>`) a null
  pointer plus or minus 0 is null and two null pointers differ by 0, both
  undefined in C. An `initializer_list`'s begin is its first element's
  address: the parser stores `&arr[0]` where CIR stores the backing
  array's (CHANGES_contb.md).

Upstream CIR has replaced the old `cir.loop` with `cir.for`/`cir.while`/`cir.do`,
and expresses RAII with `cir.cleanup.scope`. These are the operations modelled
here.

```
C++ ──clang -fclangir──▶ .cir ──cir2lean──▶ Lean AST (Gen/*.lean) ──cir_vcg──▶ proof
                                             + library models
```

## Example

```cpp
int vsum(const std::vector<int> &v) {
  int s = 0;
  for (std::size_t i = 0; i < v.size(); ++i) s += v[i];
  return s;
}
```

```lean
theorem vsum_spec (bv g : Nat) (k : BlockKind) (ty : Ty) (xs : List Int) (m : Mem)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63)
    (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hsum : Lib.PrefixSumsIn (-2147483648) 2147483647 xs) :
    Returns ctx fn_vsum.sym [.ptr (.loc bv [])] m (fun r _ => r = some (.int xs.sum)) := by
  have := hsum.succNat
  cir_start
  cir_vcg
  cir_loop (fun s i => i ≤ xs.length ∧ s = (xs.take i).sum) (fun s i => xs.length - i)
  all_goals cir_vcg
```

`Returns ctx f args m post` is total correctness: the call terminates, has no
undefined behaviour (no signed overflow, out-of-bounds or dangling access,
read of an indeterminate value, invalidated iterator, ...), returns normally,
and `post` holds of the return value and final memory. `v.size()` and `v[i]`
run against the Lean model of `std::vector`, not libc++'s code. The loop
invariant names the C++ variables `s` and `i`. Every other fact (the frame,
the types and ranges of the variables, iterator validity) is added by
`cir_loop`.

## Verified examples

| file | functions | features | time |
|---|---|---|---|
| `Examples/Basics.lean` | `add3`, `max2`, `abs_val`, `count_up`, `countdown`, `swap_ints`, `manhattan` | overflow checks, `for`/`while`, pointers into the caller, struct members | 35 s |
| `Examples/Vectors.lean` | `vsum`, `vsum_range`, `count_eq`, `find_index`, `fill_iota` | `std::vector` index loop, range-`for`, branch in loop, early return of `std::optional`, `push_back` loop into a caller's vector | 50 s |
| `Examples/Raii.lean` | `raii_scope`, `raii_loop` | constructor/destructor on early `return`; guard per iteration with `break`/`continue` | 44 s |
| `Examples/Calls.lean` | `twice`/`quad`, `count_to`/`count_plus_one`, `incr`/`incr_twice` | modular verification with `@[cir_spec]`, frame conditions, ghost values | 21 s |
| `Examples/Classes.lean` | `Account` constructor and methods, `transfer`, `open_and_use` | member functions, `this`, local objects, two objects with frame reasoning | 21 s |
| `Examples/Virtual.lean` | `rect_area`, `square_area`, `area_of` | virtual dispatch through a base-class reference, inherited overrider, specification over the dynamic type | 58 s |
| `Examples/Exceptions.lean` | `safe_get`, `guarded_get` | `std::vector::at` throwing `std::out_of_range`, `try`/`catch` by type, RAII destructor during unwinding | 30 s |
| `Examples/Exits.lean` | `checked`, `guarded_exit` | `exit` ends the program: its outcome stated with `Calls` (no `Returns` on that path), an `exit` inside a `try` block that neither the handler nor the guard's destructor sees | 5 s |
| `Examples/Misc.lean` | `arith_mix`, `ternary_chain`, `bool_logic`, `switch_fall`, `refs`, `inherit` | truncating `/` and `%`, short-circuit `&&`/`||`, `switch` fall-through, references, multiple inheritance | 73 s |
| `Examples/Carray.lean` | `sum_arr`, `find_first` | C arrays: `a[i]` as pointer arithmetic with a symbolic offset; `goto` out of a loop to a later label | 46 s |
| `Examples/Cstruct.lean` | `advance` | loop variables held in the members of a caller's struct (`c->pos`, `c->total`) | 14 s |
| `Examples/Modular*.lean` | `twice`, `quad` | per-function proofs over an abstract context (`cir2lean --modular`): each file imports only its own function; assembly with `cir_lookup` | 5 s |
| `Examples/CTests.lean` | `test_loop`, `test_count` | test functions proved by evaluation from the initial memory, no invariant (`cir_kernel`, `cir_init_mem; cir_eval`) | 15 s |
| `Examples/Link.lean` | `run` | a call across two linked translation units, each with its own `static` helper (`cir2lean --link`) | 5 s |
| `Examples/LinkAnon.lean` | `a_value` | a call across two linked units whose anonymous unions clang numbers alike with different layouts, and which share std::string's union (`cir2lean --link`) | 2 s |
| `Examples/Tokens.lean` | `fill_token` | a store to a member of an array element at a symbolic index (`&toks[i]`, the token array of C parsers) | 31 s |
| `Examples/Recursion.lean` | `sum_down`, `is_even`/`is_odd` | recursion by strong induction, mutual recursion, induction hypotheses as callee contracts | 20 s |
| `Examples/Statics.lean` | `bump` | a function writing its function-local static array: contracts over a concrete module and over an abstract context (the static's block via `ctx.gaddr`) | 10 s |
| `Examples/Ctype.lean` | `match_digit`, `match_alpha` | glibc's `isdigit`/`isalpha` macros on a symbolic character (`CIR/Std/Ctype.lean`) | 10 s |
| `Examples/PtrLoop.lean` | `str_len`, `count_char`, `has_char` | loops whose variable is a pointer walking a string, including a `do`-`while` with `*str++` in its condition | 60 s |
| `Examples/ArrLoop.lean` | `fill_local`, `fill_static`, `bump_all` | loops writing a local array, a global, and a function-local static | 40 s |
| `Examples/PtrArgs.lean` | `fill_buf`, `skip_spaces`, `copy_nonspace` | loops writing through a pointer parameter, and moving the caller's pointer through `char **` (cJSON's comment skippers) | 60 s |
| `Examples/Lists.lean` | `list_len`, `free_list` | loops over a linked list: a traversal and a loop that frees every node | 60 s |
| `Examples/TwoLoops.lean` | `fill_after_count` | a second loop after a first one: its variables through the first loop's facts (shadowed by name, used by the hypothesis itself), an array written through a pointer set before the first loop | 40 s |
| `Examples/CJAppend.lean` | `build_array` | a loop that builds a list of cJSON items (parse_array's appends at the tail, items from `cJSON_New_Item`: `malloc` + `memset`): the invariant `CJForest mem ts` over the items so far, `CJForest.snoc` for the appended one; not in `Examples.lean` | 2 min |
| `Examples/CJParseString.lean` | `parse_string` | cJSON's string parser has no undefined behaviour on any input (given `utf16_literal_to_utf8`'s contract): the scan loop keeps a ghost scan (`ScanFrom`, `CIR/Logic/CJString.lean`), the copy loop writes within `allocation_length` (`ScanFrom.window`: also when `\u` with invalid digits is consumed as six characters); the exact result of two failure paths; not in `Examples.lean` | 30 min |
| `Examples/CJDelete.lean` | `cJSON_Delete` | frees a whole cJSON item tree: recursion on the children, a loop over the siblings with a folded frame (`MemAgree`); not in `Examples.lean` | 5 min |
| `Examples/Floats.lean` | `t_conv`, `t_print`, `t_print2` | floating-point tests by kernel evaluation: conversions, `floor`/`ceil`, `float`, cJSON's `print_number` round trip (`%1.15g`, `sscanf`, `%1.17g`), `printf` conversions | 2 s |

Times are for checking each file on one core of a shared machine, ten checks
running in parallel (`lean Examples/X.lean`); `lake build Examples` checks
everything in about a minute on eight cores.
The C++ sources are in `Examples/cpp/`; `Examples/Gen/` is generated.

## Related work

Two Lean developments for ClangIR came before this one:
petr-bauch/circe (<https://github.com/petr-bauch/circe>, Lean 4, CIR to Lean,
public since 2026-09-21) and the `cir` integer and core dialect of VeIR (PR
#1346, merged 2026-09-02). ftsrg/cir2c translates real CIR to C at scale for
C model checkers. What cirlean adds: a broad fragment of unlowered CIR
(structured loops, scopes, RAII cleanups on every exit including unwinding,
classes as values, exceptions, virtual calls, `goto`, bit-fields); unmodified
`clang -fclangir` output; repository-scale coverage; native standard-library
models with iterator invalidation; loop rules with an automatic frame;
automatic proofs and preconditions (`cirinv`); and mutation testing of
specifications.

## Workflow

### 1. C++ to CIR

You need a Clang built with ClangIR (`-DCLANG_ENABLE_CIR=ON`). The examples use
an upstream build (llvm-project `4955d32b`) with the libc++ headers shipped by
ftsrg/cir2c (<https://github.com/ftsrg/cir2c>, the artifact of an ICSE 2027
submission that translates CIR to C for model checkers):

```sh
clang++ -std=c++20 -nostdinc++ -isystem <libc++>/include/c++/v1 \
  -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering f.cpp -o f.cir
```

`-fno-clangir-call-conv-lowering` keeps calls at the C++ level (structures
passed and returned by value, no pointer punning). libstdc++ headers are
supported too (the library functions are recognised by demangled name and
CIR signature).

### 2. CIR to Lean

```sh
lake build cir2lean
.lake/build/bin/cir2lean f.cir Gen.F Examples/Gen/F.lean
```

This writes one `FuncDecl` per function (`fn_<name>`), one `RecordDecl` per
class, one `GlobalDecl` per global, the `module`, and `ctx`, the verification
context. Library functions with a model are tagged (`model := some ...`) and
their bodies are never executed.

With `--modular` (`cir2lean --modular f.cir Gen.F ROOT`), every function gets
its own module `Gen.F.F.fn_<name>`, the records and globals go to
`Gen.F.Types`, and `Gen.F` imports them all and defines `module` and `ctx` as
before; `ROOT/Gen/F/manifest.json` lists each function's module, a hash of its
definition and its callees. A proof can then be stated over an abstract
context that contains the function (`ctx.mod.findFunc? "sym" = some fn_f`),
with its callees' contracts as hypotheses: it imports one function and is
checked again only when that function or a callee's contract changes.
`cir_lookup` proves the lookup facts when the proofs are assembled for the
concrete module (`Examples/Modular*.lean`). Source lines in a function module
are relative to the function, and string literals are named after their
contents (`.str.<hash>`, where clang numbers them `.str.N` in order), so an
edit elsewhere in the file leaves the module's text unchanged.

`cir2lean --link Gen.P ROOT a.cir b.cir ...` links translation units into
one module (written like `--modular`). Symbols with internal linkage
(`static` functions and globals, string literals) stay local to their unit
and are renamed `<unit>$<symbol>`; an external symbol resolves to its
definition in another unit; identical definitions in several units (inline
functions, templates) are kept once. Anonymous records, which clang numbers
per unit (`anon.N`), are named after what identifies them (`anon.<hash>`): the
member of a named record that holds one (std::string's union), else its
structure and its members' names as the unit's `cir.get_member` operations
give them (C11 6.2.7p1: anonymous types of two units are compatible only with
the same member names). So one type in two units is one record and different
ones stay apart, whatever the order of the units; two layouts of one named
record are an error.

`.lake/build/bin/cirrun f.cir func args...` runs a function on the semantics,
which is useful for testing (`CIR_TRACE=1` prints the variables at every loop
head). As around `main`, the module's global constructors run first, and a
return or `exit` is followed by the exit sequence (the `atexit` handlers and
the static destructors). A run that ends by `exit(n)` prints `n`, as `main`
returning `n` would.

### 3. Specify and prove

```lean
import CIR
import Examples.Gen.F
open CIR Gen.F

theorem f_spec ... : Returns ctx fn_f.sym [args] m (fun v m' => post) := by
  cir_start                       -- unfold the call, enter the body
  cir_vcg                         -- symbolic execution up to the first loop / to the end
  cir_loop (fun x y => inv) (fun x y => variant)   -- once per loop
  all_goals cir_vcg               -- the loop body, the code after the loop, the VCs
```

Values are `Val.int`, `.bool`, `.ptr (.loc block path)`, `.agg [fields]`
(objects), `.arr`, `.vec gen elems` (containers), `.opt` (optional). A
precondition about memory is a statement about one block, e.g.
`m.blocks b = some ⟨kind, true, .record "Account", .agg [.int bal]⟩`.

## Tactics

* **`cir_start`** turns a `Returns`/`Calls` goal into execution of the
  function body.
* **`cir_vcg`** runs symbolic execution as far as it can, then tries to close
  the remaining pure goals (`omega`, then `grind` with the list lemmas of
  `CIR.Lib`). It case-splits on data-dependent branches, evaluates memory and
  environment lookups with simprocs (no `if` cascades), and runs library models.
  It stops at loops. A goal it cannot close is left for you, stated over the
  program's values.
* **`cir_loop inv variant`** applies the loop rule on a goal whose head is a
  loop. The binders of `inv` and `variant` are C++ variable names, in any
  order:
  * a signed integer variable is an `Int`;
  * an unsigned one (`size_t`, ...) is a `Nat`;
  * a binder that is not a variable name stands for the hidden iterator of a
    range-`for` (`__begin`): a `Nat`, the element index it points to;
  * a pointer or reference variable to a `std::vector<int>` that the loop
    modifies (`out.push_back(x)`) stands for the vector's elements, a
    `List Int`;
  * `p_k`, for a pointer variable `p` to a struct whose members the loop
    modifies (`p->pos++`), stands for member number `k` (an `Int`);
  * a pointer variable `p : T*` that the loop moves (`p++`, `str += 1`)
    stands for its element index, a `Nat`: the pointer is the one at loop
    entry moved to that element of the same array (`PtrSlot`);
  * an array the loop writes stands for its elements, a `List Val`, with the
    block's kind, type and length kept (`ArrSlot`, and `cirH_len : a.length =
    n`): a local array by its name, a global by its symbol, a function-local
    static by its symbol or the part after the `.` (`re_compiled` for
    `re_compile.re_compiled`), and an array written through a pointer
    parameter `T* buf` by the parameter's name;
  * a parameter `T** input` through which the loop moves a pointer of the
    caller (`(*input)++`) stands for that pointer's element index, a `Nat`;
  * a pointer variable annotated `(p : Ptr)` stands for its value (a loop
    over a linked list: `∃ k, p = listPtr bs k`);
  * `(mem : Mem)` stands for the memory at the loop head, for loops that
    change the caller's blocks or the heap (freeing a list): the invariant
    then states what it needs about them, and the loop's frame covers only
    the function's own blocks (`LoopFrameFrom`). With either of these the
    invariant is split into its parts (`cirU_k`, witnesses `cirW_k`) and its
    pointer equations are substituted.

  Binders may carry types (`fun (str : Nat) => …`); the types are those above.
  Facts about elements are stated with `a[j]?` (`∀ j : Nat, j < i.toNat →
  a[j]? = some (.int 0)`); `cir_close` instantiates them at the indices the
  code reads.

  Variables the loop assigns before reading them (the element variable of a
  range-`for`) need no binder. `cir_loop` adds the frame itself: environment
  and names unchanged, every other block of the caller unchanged, each
  variable's type and range. The variant is any `Int`/`Nat` expression that
  decreases on every iteration (it is used as `toNat`).
* **`@[cir_spec]`**: a theorem `Returns ctx f.sym args m post` tagged
  `@[cir_spec]` is used by `cir_vcg` at every call of `f`. Its preconditions
  become goals, and execution continues from an arbitrary result satisfying
  `post`. The callee's body is never re-executed, so proofs scale with the size
  of each function, not of its call tree. `Frame m m' mods` in a postcondition
  states which of the caller's blocks the callee may change. Ghost values of a
  specification (the current contents of a pointee) are found by unification
  while the precondition is proved.
* **`cir_nlin`** (used by `cir_vcg` before `grind`): for every product of two
  non-constant integers in a goal, finds bounds of the factors by `omega` and
  adds the corner bounds of the product, so that overflow conditions such as
  `x * x ≤ 2147483647` under `0 ≤ x ≤ 1023` close automatically.
* **Test theorems by evaluation.** A test function with concrete inputs is
  proved from the program's initial memory, with no invariant:
  `Returns ctx fn_test.sym [] module.initMem (fun r _ => r = some (.int 0))`.
  * **`cir_kernel`**: the kernel evaluates `evalIter`, the approximations of
    the interpreter's fixpoint functional (taken from the definition of the
    interpreter). Every approximation is below the fixpoint, so an
    approximation's result is the interpreter's (`CIR/Logic/Kernel.lean`).
    Standard axioms only. All 16 tests of jsmn take about 7 minutes.
  * **`cir_native`**: the same check (`callReturnsB`) by `native_decide`;
    about 50 times faster, but it trusts Lean's compiler.
  * **`cir_init_mem; cir_eval`**: symbolic execution that runs every loop
    iteration by iteration (`cir_init_mem` states the initial contents of
    the module's globals). It handles partly symbolic states, but each step
    costs about 0.3 s.
  Floats reduce in the kernel: Lean's `Float` has a logical model, and the
  semantics computes the rest exactly from the bits (see Semantics). Only
  the transcendental functions of the C math library (`exp`, `sin`, `pow`,
  ...) are opaque.
* **`cir_ro_globals h`**, for `h : Module.RoGlobals module m` (the constant
  globals, string literals and `const` tables, hold their initial values),
  adds their contents as facts, for specifications over arbitrary memory.
* **`cir_lookup`** closes `ctx.mod.findFunc? "sym" = some fn_f` (and the
  other module lookups) for a concrete module by computing the lookup.
* **`cir_close`**, run on every goal `cir_vcg` leaves, also instantiates
  hypotheses `∀ x ∈ xs, P x` at the elements `xs[i]` the goal reads
  (`cir_elems`: the range of a string's characters) and removes integer
  conversions of values in range (`cir_unwrap`).
* **Facts for symbolic contracts**: `CIR/Std/Ctype.lean` gives glibc's
  character classes as ranges (`ctype_digit c : … ↔ 48 ≤ c ∧ c ≤ 57`, checked
  over all 384 table entries by the kernel); `CIR/Std/FloatLemmas.lean`
  bounds `printf`'s `%e`/`%g` text for a double that is not NaN (`fmtFloat_eg`:
  at most `P + 7` characters with precision `P`); `CIR/Std/StrtodLemmas.lean`
  reads C strings with symbolic nonzero characters (`findIdx?_isNulVal`) and
  bounds `strtod` on symbolic input: the characters consumed lie within the
  string (`strtodWith_snd_le`) and no NaN comes out of input without an `n`
  (`strtodWith_ne_nan`); `CIR/Std/FloatNaN.lean`: rounding never yields NaN
  (`decodeF_ratToFloat_ne_nan`), and `(int)x` is defined once `x >= INT_MAX`
  and `x <= INT_MIN` have failed (`floatToInt_i32_ok`), as in cJSON's
  `parse_number`.
* **`set_option cir.inline false`** makes every call of a function with a
  body require a specification (library models are still used), so a proof is
  guaranteed modular.
* **Small memory terms** (`set_option cir.normMem`, on by default). A region
  exit leaves `killRange lo hi F` in the state; symbolic execution pushes it
  into the writes of `F` (a write to one of the region's stack blocks is
  forgotten, other writes stay) and removes it below a well-formed memory
  (`(hwf : m.WF)`, or `mem.WF` in a loop invariant). A forgotten write to a
  block that was not there, and a write that a later write to the same block
  overwrites, are dropped. Lookups and frame closers then pass only through
  the live writes: `Examples/CJAppend.lean` takes 2 minutes instead of 19.
* Debugging: `set_option cir.traceSteps true` logs steps slower than 200 ms;
  `cir.nosplit` stops at the first stuck match instead of splitting;
  `cir.fuel n` bounds the number of steps; `cir_step` runs one step.

## Values in contracts

* Memory: `m.blocks b = some ⟨kind, alive, ty, val⟩`, with `kind` one of
  `.stack .heap .global .readonly .exn`. Values: `.int x`, `.bool b`,
  `.float f`, `.ptr p`, `.arr vs` (arrays), `.agg vs` (records and unions,
  members in order), `.vec g vs` (`std::vector`, `std::string`), `.opt o`,
  `.undef` (indeterminate).
* Pointers: `.loc b path`, where `path` steps into arrays and records with
  `.idx i` and into containers with `.vel g i`; `.null`; `.fn "sym"` (a
  function pointer: cJSON's `global_hooks` holds `.fn "malloc"`, `.fn
  "free"`, `.fn "realloc"`; a call through it calls `sym`, by its body,
  model or `@[cir_spec]`); `.addr a` (an integer used as a pointer).
* Unions: `.agg vs` with one entry per member, in declaration order; the
  active member holds its value and the others `.undef`. Forming a pointer to
  a member (`u.ch`, `&u.ccl`) or storing through one makes it the active one
  (an `.undef` member takes the bytes the previous member holds, see
  Semantics, else its type's initial value) and the others `.undef`; a load of
  an inactive member reads the active one's bytes the same way. tiny-regex-c's
  `regex_t` element is
  `.agg [.int type, .agg [.int ch, .undef]]` with `ch` active, or
  `.agg [.int type, .agg [.undef, .ptr ccl]]` with `ccl` active; a
  zero-initialised static union has its first member zero (`.agg [.int 0,
  .undef]`).
* Constant tables (`static const char *types[] = {"UNUSED", …}`, string
  literals): `cir_ro_globals h` with `h : Module.RoGlobals module m` adds
  their initial contents as facts; an entry at a symbolic index `t` is read
  after a case split on `t` (`rcases` on `t < 17`, or `cir_eval` with `t`
  concrete).
* Linked lists: the nodes' blocks in order, `bs : List Nat` (distinct,
  `bs.Nodup`); `listPtr bs k` is the pointer to node `k` (null past the end)
  and `bs.length - listIdx bs p` a loop variant. Facts about the nodes are
  quantified over the index, `∀ k (h : k < bs.length), m.blocks bs[k] = …`;
  symbolic execution uses such facts as conditional rewrite rules at the node
  it reads, and `(hwf : m.WF)` lets it tell the caller's blocks from the ones
  allocated since the call. cJSON item trees: `CJ` (a ghost copy of the
  items) and `CJForest m ts` (`CIR/Logic/CJTree.lean`), with
  `CJForest.frame`.
* Loops that free or rewrite the nodes of such a list state their frame
  folded, `MemAgree mem m P`: the memory agrees with the caller's `m` on the
  blocks satisfying `P` (for a loop freeing the items in order,
  `b < m.next ∧ b ∉ CJ.forestBlocks (ts.take k)`). As a rewrite rule, a fact
  `∀ b, … → mem.blocks b = m.blocks b` would be tried, and fail, at every
  block read. Each iteration first derives ground facts about the item it
  reads (`σ.mem.blocks ts[k].b = …`); `cir_agree_step` (`MemAgree.cj_step`)
  moves the frame across an iteration, `MemAgree.cj_done` out of the loop,
  `cir_wf` proves well-formedness of the memory, and `cir_refute_mem` closes a
  path on which a lookup through the iteration's writes was not evaluated
  (`CIR/Tactic/Frame.lean`). Example: `cJSON_Delete` (`Examples/CJDelete.lean`).
* Loops that build such a list (cJSON's `parse_array`): the invariant names
  the items built so far, `∃ ts, CJForest mem ts ∧ head = listPtr (ts.map
  CJ.b) 0 ∧ current_item = listPtr (ts.map CJ.b) (ts.length - 1) ∧ …`; an
  iteration's new list is `ts ++ [t]` (`CJForest.snoc`: the new item's
  record, the old tail's `next` linked to it, the other blocks unchanged),
  each premise a lookup through the iteration's writes (`cir_simp_frame`).
  Example: `Examples/CJAppend.lean`.
* Globals: in a concrete module, `ctx.gaddr "sym"` is the global's index,
  which is its block in `module.initMem` (`cir_lookup` computes it). Over an
  abstract context, state `(hg : ctx.gaddr "sym" = some b)` and the block's
  contents (`m.blocks b = some ⟨.global, true, ty, v⟩`); `cir_vcg` uses both.
  Linked internal symbols are named `<unit>$<sym>`.

## Proofs without specifications: `cirinv`

`tools/cirinv_v5.py --cir f.cir --sym SYMBOL --out DIR [--json OUT.json]`
proves that a function has no undefined behaviour, or finds an input that
has some, without a specification:

1. It runs the function on the semantics (`cirrun`) on sample inputs: small
   values, values around vector lengths, type extremes. It records the
   variables at every loop head and every input with undefined behaviour.
2. If some input has undefined behaviour, it infers a precondition. That is
   a conjunction of simple facts about the parameters (sign, a magnitude
   bound 2^k - 1, non-zero, an index below a vector length or a program
   constant, the order of two parameters) that excludes every such input
   while excluding few others. It then samples inputs that satisfy the
   precondition and repeats with every new undefined case.
3. It states the theorem "no undefined behaviour" for arbitrary arguments
   (integers in their type's range; vectors, arrays and pointees in live
   blocks) under the precondition.
4. It runs Houdini over candidate loop invariants and variants mined from
   the traces: Lean reports the candidates that are not inductive
   (`cir_houdini_report`), they are dropped, and the step repeats.
5. It writes the proof script and checks it without `sorry`.

The result is `proved`, or `proved_under` (with the precondition; the
reported inputs lie outside it and have undefined behaviour), or
`ub_witness` (an input with undefined behaviour and no proof under an
inferred precondition), or `goals_left` (no undefined input found; the goals
Lean could not close are reported), or `recursive` (functions that reach a
recursive function need a specification by induction). A precondition is
sufficient (the Lean proof) but not necessarily the weakest one.

`tools/cirinv_batch_v2.py` runs it over a corpus (sharded, one core per
shard) and `tools/cirinv_contracts.py` writes the inferred preconditions in
C++ syntax. On the 176 in-scope functions of TheAlgorithms/C-Plus-Plus
@fdcc29b with at most one loop:

| result | functions |
|---|---|
| proved | 24 |
| proved under an inferred precondition | 17 |
| input with undefined behaviour, no proof | 56 |
| goals left | 34 |
| recursive (needs a specification) | 36 |
| other (no loop reached, timeouts, errors) | 9 |

Examples: `math::rect_area<uint16_t>(w, h)` has no undefined behaviour for
`w <= 32767` (for `(65535, 65534)` the product overflows `int` after integer
promotion); `md5::leftRotate32bits(x, r)` requires `1 <= r && r < 32`;
`Max(int *Arr, int N)` requires `N` elements behind `Arr`;
`search::binary_search::binarySearch(arr, val)` has undefined behaviour on
sorted input whenever `val` is below every element (`high = m - 1` wraps
around, then `arr[m]` is out of range), e.g. `([2, 15], 0)`, and no
precondition of the supported shapes avoids it.

## Coverage: `cirscan`

`cirscan --json f.cir` classifies every user function: in scope (every
reachable call has a body or a library model, and every operation is
modelled), or the calls and operations that are missing. On
TheAlgorithms/C-Plus-Plus @fdcc29b, 357 of 361 files go through ClangIR and
`cir2lean`, and 1765 of the 2055 non-test user functions are in scope. Most
of the rest use `std::string` members without a model, `shared_ptr`
internals, file streams or input streams.

## Library models (`CIR/Std/Models.lean`)

| C++ | Lean value | operations |
|---|---|---|
| `std::vector<T>` | `Val.vec gen (elems : List Val)` | constructors (default, copy, move, initializer list, size, fill, an iterator range of pointers or vector iterators: libc++'s, whose enable_if c++filt cannot demangle, recognized structurally; the range must lie within one array or container), destructor, assignment (copy, move, initializer list), `assign` (n copies, an iterator range of pointers or vector iterators; the value or the range in the vector itself is undefined, [sequence.reqmts]; CHANGES_contb3.md), `size`, `empty`, `[]`, `at` (throws), `front`, `back`, `data`, `begin`, `end`, `push_back`, `emplace_back` (of one element; other constructor arguments are not modelled), `pop_back`, `clear`, `resize`, `reserve`, `swap`; an object pointer that designates an array of vectors or strings, or a byte view of one at an element boundary, designates that element (also for `std::string`; CHANGES_contb.md); a `std::vector` object that holds libc++'s members of an empty vector, all null or zero, where no constructor of the model ran (a constant-initialized global or static: `vector()` is `constexpr`, so no dynamic initialization calls it; a defaulted constructor that CIR spells as the member stores) is an empty vector (CHANGES_vecfix.md) |
| `std::vector<bool>` (libc++) | `Val.vec gen (bools : List Val)`; the reference proxy (`__bit_reference`, `__bit_const_reference`) is `Val.agg [.ptr element, .int 1]` | `std::vector<T>`'s constructors (also with an allocator; the iterator range of `bool` pointers), destructor, assignment, `assign(n, x)`, `size`, `empty`, `push_back`, `pop_back`, `clear`, `resize`, `reserve`, `swap`; `[]` (also `const`) and `at` (throws) return the proxy, whose `operator bool`, `operator=(bool)`, `operator=(const __bit_reference&)` and `flip` read and write the element (a proxy into a vector that reallocated is undefined, as a reference is); `==`. Iterators, `front`, `back`, the vector's `flip`, `assign(first, last)` and `emplace_back` are not modelled: libc++'s code stops at the vector's value. libstdc++'s `std::vector<bool>` runs its own code (CHANGES_vecfix.md) |
| iterators over contiguous storage | `Val.agg [.ptr p]` | `*`, `++`, `--`, `==`, `!=`, `<`, `-`, `+ n`, `base`, and libc++'s `std::__to_address` (how `std::sort`, `std::copy`, ... unwrap them; `end()` included); `*` and `->` of `end()` are undefined |
| `std::string` | `Val.vec gen (chars ++ [0])` | constructors (default, C string, copy, move; libc++'s of `n` copies of a character and from an iterator range of `char` pointers, contiguous iterators or their reverse iterators), `size`, `empty`, `[]`, `at`, `push_back`, `append`/`+=`, `reserve` (the capacity is not modelled, so as for a vector every pointer into the string is invalidated), `c_str`, `==`, `begin`/`end`, assignment, `swap`, `+` (libc++'s `__concatenate_strings`, and the `operator+(const char*, const string&)` its library exports), `compare(const char*)` and `compare(pos, n1, const char*, n2)` (from libc++'s library; `==` with a C string; `<` and `compare` of two strings run libc++'s code, `memcmp` over the characters); each character copied or compared is read as a `char` (an indeterminate one is undefined) |
| `std::optional<T>` | `Val.opt (Option Val)` | constructors (`nullopt`, value, copy), `has_value`/`operator bool`, `*`, `value` (throws), `value_or` |
| `std::unique_ptr<T>` | `Val.agg [.ptr p]` | constructors (null, pointer, move), `get`, `*`/`->`, `reset`, `release`, `operator bool`, destructor (frees) |
| `std::min`, `std::max`, `std::swap`, `std::move` | | |
| `std::sort` of an arithmetic type with `less` | libc++'s library instantiations `std::__sort<__less<T, T>&, T*>` (other comparators run libc++'s inline introsort) | ascending, in place; undefined for a range not within one array, an indeterminate element or a NaN; a range holding both -0.0 and +0.0 is not modelled (their order depends on the introsort) |
| the unordered containers, `std::hash` of string views, `__gnu_cxx::hash<const char *>` | libc++'s library functions `std::__hash_memory`, `std::__next_prime` | `__hash_memory(p, n)`: CityHash64 as libc++ computes it (ABI version 1) of the `n` bytes of the representation of the object `p` points into, undefined past its end and for an indeterminate byte or a pointer's byte; the characters of a `std::string`, a container here, are not read (not modelled); `__next_prime(n)`: 0 for 0, else the smallest prime not below `n` (its `overflow_error` is not modelled) |
| `operator new` / `delete` (also array and aligned forms) | heap blocks | |
| C I/O | `printf`, `fprintf`, `vprintf`, `vfprintf`, `puts`, `putchar`, `fputs`, `fwrite`, `getchar`, `fread`, `ungetc`, `scanf`, `fscanf`, `fflush`, `perror` | output not modelled; the result is the character count of the text `sprintf` would produce; `fputs` and `fwrite` to `stdout` or `stderr` return glibc's results for everything written (1; the count, 0 when the size or the count is 0), `fwrite`'s bytes lying in one object (indeterminate ones included); `fflush` returns 0 (there are no buffers) for `stdout`, `stderr` and a null pointer, and is undefined for `stdin`, an input stream (C11 7.21.5.2p2), and for anything else, no stream (7.1.4p1); `perror`'s argument is a null pointer or a string, and `errno` is indeterminate after it (C11 7.5p3 lets it set any nonzero value; glibc leaves EINVAL when `stderr` is not open for reading); standard input is empty: `getchar` returns EOF, `fread` from `stdin` reads nothing and returns 0 (its buffer must still be valid), `ungetc` of EOF onto `stdin` fails (EOF; a character pushed back is not modelled), and `scanf` (also glibc's `__isoc99_scanf`, `__isoc23_scanf`) and `fscanf` on `stdin` return EOF, as `sscanf` on an empty string, unless the format holds only white space and `%n` (0); any other stream is not modelled (no file is ever opened); `fprintf`'s stream must not be null: `stdin`, `stdout` and `stderr` are distinct non-null handles that nothing reads through |
| formatted text | `sprintf`, `snprintf`, `vsprintf`, `vsnprintf` | conversions `d i u o x X c s f F e E g G %` with flags (`- + space # 0`), width and precision (digits or `*`; `%s` with a precision reads at most that many characters, which need no terminator), length modifiers `hh h l ll j z t`; the combinations C11 leaves undefined (`#` with `d i u c s`, a precision with `c`, `0` with `c s`, a length modifier the conversion does not take) are undefined. With a string literal as the format (a constant array; a `static char fmt[]` the program may change is not one; also for `printf`, `fprintf`), an argument of another type than its conversion needs after the promotions is undefined (7.21.6.1p9), one of the other signedness unless its value fits both; a format that is not a literal is not checked for that. The `v` versions (also `vprintf`, `vfprintf`) format the arguments that an initialized `va_list` has not given to `va_arg` yet, and check each one its call passed with its type in the same way, at run time, whatever the format (through a function pointer only the kinds of the values are checked). Floating-point conversions are exact: the digits of the double's binary value, rounded to nearest-even, `%g`'s style choice, as glibc (checked on 200k random doubles); a NaN is not modelled (glibc prints its sign, which Lean's `Float` does not keep); the format string or a `%s` string (with a precision, the characters it reads) overlapping the text written is undefined; `%s` of a character object that is no array element reads it as an array of one (C11 6.5.6p7); `%lc` converts as wcrtomb does in the C locale, whose wide characters are ASCII (glibc): any other is an encoding error, the result is -1, `errno` is EILSEQ, and the text before it and a terminator are written, as glibc does |
| formatted input | `sscanf` | conversions `d i u x X f F e E g G a A n %` with `*`, width and length modifiers (`%x` takes an optional `0x`; `%i` reads in base 0 as strtol does: `0x` and hexadecimal digits, a leading 0 and octal digits, else decimal digits, while a `0b` prefix, binary for glibc's C23 `__isoc23_sscanf` and the end of the number for `__isoc99_sscanf`, is not modelled); glibc's rule for floating-point items (the longest prefix of a subject sequence is read and must be complete: `1e+` fails); EOF before the first conversion; each target object, the one that a store of the program through the pointer reaches (a structure's first member, an array's element 0, a byte for `%hhd` and `%hhu`), has exactly the conversion's type (C11 7.21.6.2p10-12: `%d` and `%i` an `int`, `%u` and `%x` an `unsigned int`, signedness included) and is written like such a store; `%u` and `%x` have strtoul's value (p12): a negative number is negated in `unsigned long`, so `-1` is `ULONG_MAX`, which only an `unsigned long` holds; after a floating-point item stored as an infinity, a zero or a subnormal (glibc may store `strtod`'s ERANGE) `errno` is indeterminate, so reading it is undefined |
| number parsing | `strtod`, `strtof`, `atof`, `atoi`, `atol`, `atoll` | `strtod`: decimal and hexadecimal numbers, `inf`/`infinity`, `nan(...)`, correctly rounded to the format; `*end` after the subject sequence, a typed store (the object must hold a pointer, C11 6.5p7); ERANGE in `errno` as glibc stores it, for an overflow and for an underflow (a nonzero value tiny after rounding and inexact). `atof`: `strtod`'s value, but one that overflows cannot be represented, which is undefined (C11 7.22.1p1). `atoi`: `strtol`'s base-10 subject sequence; a value outside the result type is undefined (C11 7.22.1.2) |
| integer parsing | `strtol`, `strtoul`, `strtoll`, `strtoull`, and glibc's `__isoc23_` versions | white space, a sign, bases 0 and 2..36 with their prefixes (`0x`; `0b` only in the `__isoc23_` versions, which glibc 2.38+ headers call under `_GNU_SOURCE`); a value out of range gives the bound in the direction of the sign and ERANGE in `errno`, and `strtoul` negates in the unsigned type; `*end` after the subject sequence (`s` when there is none), a typed store as for `strtod` |
| glibc `<ctype.h>` tables | `__ctype_b_loc`, `__ctype_toupper_loc`, `__ctype_tolower_loc` | read-only C-locale tables (glibc's `isdigit` etc. are macros over them) |
| varargs | `va_start`, `va_arg`, `va_copy`, `va_end` | the arguments after the parameters keep the types the call gives them (after the default promotions), structures included; `va_arg` of a type an argument was not passed with (C11 7.16.1.1p2: signed/unsigned of one integer type and `void *`/`char *` are allowed), or past the end, is undefined; a call through a function pointer passes values only, checked by kind; a copy reads on independently. A `va_list` is initialized by `va_start` or `va_copy` and ended by `va_end` in the same function, before it returns and before the block of the `va_list` ends (7.16.1p1): `va_arg` on one not initialized or ended, `va_start` or `va_copy` into one initialized, `va_end` without either or in another function, a return or the end of its block (also by `break`, `continue`, `goto`) with one of the function's own still initialized, its owner's use (but `va_end`) after another function's `va_arg` on it, and any other function's but the one that went on with it (7.16p3; a `v*printf` call by the owner is not caught, as a model does not see its caller), and any use but `va_end` after a `v*printf` call on it, which leaves its value indeterminate (7.21.6.8p2), are undefined. A `va_arg` through a pointer to the `va_list` (`va_arg(*pap, T)`, footnote 253) leaves the list its owner's to go on with |
| C math library | `sqrt`, `pow`, `exp`, `exp2`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`, `floor`, `ceil`, `trunc`, `round`, `rint`, `nearbyint`, `lrint`, `llrint`, `fmod`, `fabs`, `cbrt`, `fmin`, `fmax`, `copysign` and their `float` versions, `hypot`, `hypotf`, `expm1`, `log1p`, `erf`, `erfc`, `tgamma`, `lgamma` | `sqrt`, `floor`, `ceil`, `trunc`, `round`, `rint`, `nearbyint`, `fmod`, `fabs`, `fmin`, `fmax`, `copysign` exact (IEEE); `rint`, `nearbyint`, `lrint` and `llrint` in the default rounding mode (to nearest, half to even), `lrint` and `llrint` undefined where their value is unspecified (out of range, an infinity or a NaN); the transcendental functions call the C library through Lean's `Float`, and their `float` versions call the C library's `float` functions (`sinf`, ..., `powf`, `atan2f`) through Lean's `Float32`, so they give glibc's results bit for bit, not the double function's result rounded to `float`, which differs by one unit in the last place on millions of inputs; `hypot`, `hypotf`, `expm1` and `log1p`, which Lean's `Float` lacks, are computed as glibc 2.43 computes them on the reference machine, bit for bit: its libm is an x86-64-v3 build, so the code takes its fused multiply-add paths and GCC fuses products into sums, and the model performs the same operations in the same order (`CIR/Std/Libm.lean`); `erf`, `erfc`, `tgamma` and `lgamma`, which glibc 2.43 computes with CORE-MATH's correctly rounded code, are the double nearest to the exact value: an interval with dyadic ends encloses it, from series with bounded remainders, at a precision that doubles until both ends round alike (undefined if that takes more than 2048 bits; `tgamma` of an integer is rounded from the exact factorial); `lgamma` stores glibc's sign of `Γ(x)` in `signgam` (`CIR/Std/LibmCR.lean`). `errno` as glibc's (C11 7.12.1, `MATH_ERRNO`): EDOM for a domain error (a NaN from arguments that are not NaNs), ERANGE for a pole or an overflow (an infinity from finite arguments); after a possible underflow (a subnormal result, or 0 from `exp`, `exp2`, `pow`, `atan2`, `erfc` or `tgamma`), where glibc's rule differs between functions, it is indeterminate, so reading it is undefined |
| complex multiplication and division | `__muldc3`, `__divdc3`, `__mulsc3`, `__divsc3` (`CIR/Std/Complex.lean`) | the model follows the installed libgcc, the library native programs link here (GCC 15's `libgcc2.c`, built for x86-64-v3, with its fused multiply-adds): the products with Annex G's recovery of infinities from NaN + iNaN; the quotient by Smith's method with McGehearty's scaling, then the recovery of infinities and zeros; `float` division in `double`. It differs from a libgcc built without fused products (in the last bit of some quotients) and from compiler-rt, which divides by another method (scaling by `logb` / `scalbn`). A NaN has no sign here: where libgcc copies a NaN's sign bit into a zero, the zero is +0. `__mulxc3`, `__divxc3` (`long double`) have no model |
| `signal` | registers a handler and returns the one before it (`SIG_DFL` at startup), or `SIG_ERR` for a signal glibc does not let a program handle | registering only: no signal is ever delivered (`raise`, `kill` and hardware traps are not modelled) |
| C strings | `strcmp`, `strncmp`, `strcpy`, `strncpy`, `strcat`, `strchr`, `strrchr`, `strdup`, `realloc` | `strchr` and `strrchr` (the first and the last occurrence) on a string in a char array (the terminator is found for `c` = 0); `strncpy` writes n characters, those of the string up to its terminator and then null characters (no terminator when the string has n characters or more); `strcpy`, `strncpy` and `strcat` into a destination too short for what they write, or between overlapping objects, are undefined (C11 7.24.1p1, 7.24.2.3, 7.24.2.4, 7.24.3.1); `strdup` copies into a fresh heap array (allocation succeeds) |
| `setjmp`, `longjmp` (also `sigsetjmp`, `siglongjmp`, `_longjmp`) | non-local jumps (see Non-local jumps below) | |
| C library | `malloc`, `calloc`, `posix_memalign`, `free`, `strlen`, `memset`, `memcpy`, `memmove`, `memcmp`, `memchr` | untyped heap storage gets its type at the first cast (an array of `T` when the size is a multiple of `sizeof(T)`); `posix_memalign` allocates as `malloc` when the alignment is a power of two and a multiple of `sizeof(void *)`, else returns `EINVAL`; `memchr` reads the characters of a char array one by one up to the first match (C11 7.24.5.1), and the bytes of any other object's representation, as `unsigned char`, from the byte its argument points to in the complete object (an indeterminate byte, a pointer's byte, reading past the object and a union member's bytes are undefined); `memset` (zero, or a char fill) and `memcpy`/`memmove` work on values over whole objects of one type, also the live elements of a `std::vector` or `std::string` (the element type from the container's type; what `std::copy` of a trivially copyable range does), otherwise on the bytes of the objects' representations (objects of other types, part of an object; not unions, not container storage): a pointer is copied only with all its bytes, in order, and an indeterminate byte leaves its scalar indeterminate (CHANGES_memb.md); `memcmp` on the bytes of two ranges of one scalar type (as `std::equal` and the containers' `==` compare trivially comparable elements; a pointer's bytes are not modelled), returning glibc's result, the difference of the first differing bytes as `unsigned char` (only its sign is specified, C11 7.24.4.1p2); a pointer argument must be valid also when the length is 0 (C11 7.24.1p2: not null, not dangling, a destination not read-only), except in the C++ library's own calls (from the body of a `std::` or `__gnu_cxx::` function defined in the library's headers, not a program's specialization of a standard template: libc++ relocates and copies empty ranges through null pointers), where a length of 0 reads and writes nothing (CHANGES_contb3.md) |
| pseudo-random numbers | `rand`, `srand`; POSIX `lrand48`, `seed48` | glibc's generator (`random_r`, `TYPE_3`: 31 words, `r[i] = r[i-3] + r[i-31]` mod 2^32, the result `r[i] >> 1`; `srand` seeds as glibc does, 310 outputs discarded; without `srand` the state of `srand(1)`), so the values are glibc's; `RAND_MAX` is 2^31 - 1. `lrand48`: glibc's 48-bit generator, `X = (0x5DEECE66D X + 0xB)` mod 2^48 from `X` = 0, the result `X >> 17`; `seed48` sets `X` from three `unsigned short`s (least significant first) and returns glibc's static copy of the previous `X` (`lcong48`, which changes the constants, is not modelled) |
| bit search | POSIX `ffs`; glibc's `ffsl`, `ffsll` | the position, from 1, of the least significant bit set, 0 for 0 |
| `abort`, `__assert_fail`, `__cxa_pure_virtual` | undefined behaviour: a proof shows they are never reached (every `assert` holds, no pure virtual function is called) | |
| `exit`, `_Exit`, `quick_exit` | program termination with the status (`Exit.halt`) | no cleanup runs and no handler catches it; `exit` is followed by the exit sequence, as a return from `main` is; `_Exit` and `quick_exit` skip it, and `quick_exit` runs the `at_quick_exit` handlers instead; `exit` or `quick_exit` during the exit sequence or in an `at_quick_exit` handler is undefined |
| `atexit`, `__cxa_atexit`, `at_quick_exit` | registration for the exit sequence (the last registered runs first, one registered meanwhile included; `__cxa_atexit` registers the destructors of static objects, whose return ends the object's lifetime: a later use is undefined, C++ [basic.life]p7), and for `quick_exit` (`at_quick_exit`, likewise) | |
| `__cxa_guard_acquire`, `__cxa_guard_release`, `__cxa_guard_abort` | guarded initialization of static locals, inline variables and static data members of templates | one thread; a recursive initialization is not detected |
| `std::ostream` output (`std::cout << ...`, `std::endl`) | no effect on the modelled state; returns the stream, which must be an object | C-string and `std::string` arguments must be valid |
| `<ctype.h>` | `isdigit`, `isalpha`, `isalnum`, `isspace`, `isupper`, `islower`, `isxdigit`, `ispunct`, `isprint`, `toupper`, `tolower` | C locale; the argument must be EOF or an `unsigned char` value |
| standard exception classes | constructors and destructors of `std::logic_error`, `std::runtime_error`, `std::length_error`, `std::out_of_range`, ...; `what()` of `std::exception` and `std::bad_alloc` | the message is not modelled; the two `what()` strings are fixed ("std::exception", "std::bad_alloc"), one read-only string per class, as the libraries return a literal |
| libevent 2.1 buffers | `evbuffer_new`, `evbuffer_free`, `evbuffer_add`, `evbuffer_get_length` | a buffer is a library object: a heap block holding its bytes, which the program can only pass back to the library; `evbuffer_add` reads a `char` range, its pointer valid also for length 0; freeing a buffer twice is undefined; allocation succeeds |
| libevent 2.1 HTTP | `evhttp_add_header`, `evhttp_send_reply` | `evhttp_add_header`: -1 for a key or a value holding CR or LF (libevent 2.1.12 refuses folded values too); else an entry with heap copies of the key and the value goes to the end of the `struct evkeyvalq` list (typed stores; the program can walk it), and 0 (allocation succeeds). `evhttp_send_reply`: a heap `struct evhttp_request` of libevent 2.1's layout; the request is freed with what it owns (header lists, buffers, strings): at once when it has no connection, `databuf` left as it is; with one, after `databuf`'s bytes move into the reply (`databuf` is then empty), since the request is libevent's from then on. A request whose freeing is deferred (`EVHTTP_REQ_DEFER_FREE`) is not modelled |
| libevent 2.1 event loop | `event_base_loopbreak` | -1 for a null base, 0 for a live one; the loop itself is not modelled |
| POSIX threads | `pthread_self`, `pthread_equal` | one thread, whose id is 1; `pthread_equal` compares the ids, as glibc does |
| scheduling | `sched_get_priority_max`, `sched_get_priority_min`, `pthread_setschedparam` | Linux's values: 99 and 1 for `SCHED_FIFO` and `SCHED_RR`, 0 for `SCHED_OTHER`, `SCHED_BATCH`, `SCHED_IDLE`, `SCHED_DEADLINE`, `SCHED_EXT`, else -1 and EINVAL in `errno`. `pthread_setschedparam` of the thread's id (any other is undefined): EINVAL for a policy that is not one (`SCHED_RESET_ON_FORK` aside), for `SCHED_DEADLINE`, for a priority outside 1..99 with `SCHED_FIFO` and `SCHED_RR` or other than 0 with the others; else 0, the thread being allowed the real-time policies (EPERM without the privilege); the result is the error number, which glibc also stores in `errno`; the policy is not kept (Linux also wants the privilege to leave `SCHED_IDLE`) |
| `errno` | `__errno_location` | the program's `errno`, an `int` global that the frontend adds to a module declaring `__errno_location` (one per linked program), 0 at program start (C11 7.5p3) |
| error messages | `strerror_r` (GNU's, `_GNU_SOURCE`) | glibc's message (x86-64 Linux, error numbers 0 to 133), a string of its own with `buf` unused; else "Unknown error N" written to `buf` as `snprintf` would, and `buf` |
| time | `time`, `ctime_r` | `time`: the clock, also stored through a non-null argument (a typed store). `ctime_r`: `asctime`'s text of the local time ("Thu Jan  1 00:00:00 1970\n"; the time zone is UTC) into `buf`, a char range of the text's length; as glibc, null with EOVERFLOW in `errno` when it needs more than 26 bytes (`buf` then holds its first 25 characters), and null with EINVAL for a year that `struct tm` cannot hold |

The generation number `gen` changes on every operation that may reallocate
(`push_back`, `clear`, assignment, ...), so a pointer or iterator into the old
storage no longer resolves. This is stricter than C++ (some iterators stay
valid), hence sound.

Adding a model: `Std.runModel`'s `match` is at the limit of the automatic proof
that it preserves well-formedness (`WF_runModel`, `CIR/Logic/WFGlobal.lean`),
which runs out of heartbeats with one more alternative of its own, even one
whose arguments are not matched. A new model joins `LibOp` (`Model.lib`, run by
`Std.libModel`, whose own `match` is small), or a helper of its own behind one
alternative, with a well-formedness lemma and a head-checked `cir_wf_term`
rule (as `vecBoolModel`, `longjmpModel`); a global `cir_wf_close` rule slows
every goal of `WF_runModel` and made it time out too.

## Semantics (`CIR/Semantics/`)

* **Interpreter.** `evalOp`/`evalRegion`/`evalCall` are defined with
  `partial_fixpoint` in the monad `Res` (`ok` / `ub msg` / `div`), so
  non-termination is a value and the definitions need no fuel.
* **Memory.** Blocks of structured values (`CIR/Memory.lean`). A block has a
  kind (stack/heap/global/readonly/exception), a liveness flag, its type, and
  a value. Leaving a region frees the stack blocks allocated inside it, and
  `cir.stackrestore` the variable-length arrays allocated since its
  `cir.stacksave`; a variable-length array of zero or negative size is
  undefined (C11 6.7.6.2p5). A const-qualified local object
  (`cir.alloca ... const`, `Op.allocaConst`: of scalar, pointer or array
  type, in C also a structure of such members; not a parameter, not a
  variable that a loop, a backward `goto` or a `longjmp` initializes again)
  is a read-only block that only its initialization writes, filling its
  indeterminate positions (C11 6.7.3p6); it outlives its region, so an
  access through a pointer to it after the region has exited is not
  detected, nor is a write to a constant global whose initializer is not
  modelled (an indeterminate value). Reads
  of indeterminate scalars, writes to read-only blocks (except that
  initialization), out-of-range element
  access, use after free and stale container pointers are undefined. In a
  C++ module, a `cir.store` or `cir.copy` of a type with no value
  representation (a record whose members are padding, empty members or such
  records, or an array of them) writes nothing, so the frontend drops it
  (`Frontend.dropEmptyStores`): an empty class object has no value bits
  ([intro.object]p9) and may share its address with another member
  ([dcl.attr.nouniqueaddr]), and CIR's records leave such a member out and
  store its value through a cast of the shared address (libc++'s
  allocators and comparators in compressed pairs, as `map`, `set` and `list`
  copies build them). C has no empty structures (only as a GNU extension):
  a C module keeps those operations.
* **Runtime representation.** Compiled code (`cirrun`, `cirscan`) keeps a
  memory's blocks in a persistent hash map behind the function `Mem.blocks`:
  `Mem.empty`, `setBlock`, `alloc`, `allocAs`, `endScope` and `Std.fresh` are
  implemented (`@[implemented_by]`) by the operations of `CIR.MemRT`
  (`CIR/Memory.lean`), whose memories have a run-time cell of six fields and
  a flag, cast to `Mem`. Fields 0 and 1 are `Mem`'s `blocks` (a lookup in
  the map) and `next`, which the rest of the compiled code reads; field 2 is
  the map, field 3 the reference chain of `CIR_MEMCHECK`, field 4 the
  closure of field 0 again, field 5 the ids of the stack blocks, the latest
  first, and the flag says whether that list is complete. Invariant: when
  fields 0 and 4 are the same object (pointer-equal), field 2 holds exactly
  the blocks of field 0 and, under the flag, field 5 the id of each of its
  stack blocks; any other `Mem` has its map and list built from `blocks`
  over `[0, next)` (every reachable memory is well formed). A lookup costs
  O(log n) in the number of blocks instead of a walk over every update since
  the block's last write, which made loops quadratic; a region exit pops the
  ids from its first one up off the list and removes those stack blocks,
  so it visits only the blocks it removes (a stack block written where none
  was ends the flag, and the exits then visit every id the region
  allocated), and one that allocated no stack block allocates nothing. The
  bounds of the integer types, which every arithmetic result and store is
  checked against, are computed by `intMinFast`, `intMaxFast` and
  `wrapFast`, which take the powers of two of the widths 8, 16, 32 and 64
  from a table (`pow2Fast`); `@[csimp]` replaces `intMin`, `intMax` and
  `wrap` by them in compiled code, by a proof that they are equal. Proofs,
  the kernel and symbolic execution use the definitions, which are
  unchanged, and no proof runs compiled code (`native_decide` occurs only in
  the `cir_native` tactic, which no proof uses). With the environment
  variable `CIR_MEMCHECK` set, every memory also carries the closure chain
  that the definitions build, and every lookup checks that the map gives the
  same block object, or none on both sides: a divergence prints a message,
  appends it to the file `CIR_MEMCHECK_LOG` names, if set, and ends the
  program with exit status 97.
* **Integers** are mathematical integers with range checks: signed overflow
  (`nsw`) is undefined; unsigned arithmetic wraps; division truncates; shifts
  follow C. `cir.clz`/`cir.ctz` count zero bits (with `poison_zero` the result
  for 0 is indeterminate: a use of it is undefined, `__builtin_clzg`'s
  fallback is not); `cir.popcount`, `cir.parity`, `cir.ffs`, `cir.clrsb`,
  `cir.byte_swap`, `cir.bitreverse` and `cir.rotate` are exact;
  `cir.is_constant` (`__builtin_constant_p`) is false. Atomic operations
  (`cir.atomic.*`) run one at a time (one thread); a compare-exchange whose
  failure order is release or acq_rel, or (in C only) stronger than its success
  order, is undefined (C11 7.17.7.4p2; C++ [atomics.types.operations] has the
  first rule only, since C++17 (P0418R2), and C23 dropped the second too), but
  clang turns a release or acq_rel failure order into relaxed before the CIR.
* **Pointer arithmetic and bytes.** A stride counts objects of the pointer's
  type (C11 6.5.6p8). For every type but the character types it is read
  strictly: an array element moves within its array (up to one past its
  end); a pointer to an object that is no array element moves within an array
  of one, the object and one past it (6.5.6p7), so `&s.a + 1` may be formed
  and compared but not dereferenced, even at the address of `s.b`, and
  `(int *)s + 1` over an array of two-`int` structures is one past `s[0].x`.
  A pointer to an array object used as a pointer to its element type is one
  to element 0. A stride in other units than an array's elements
  (`(short *)a + 2` over an `int` array) moves by bytes within the array; only
  a character access is defined at a position between elements. Character
  pointers move over the bytes of the complete object (6.2.6.1p4, 6.3.2.3p7),
  and a pointer converted back after character arithmetic designates the
  subobject that starts at that byte (in a union, in its active member):
  `offsetof` arithmetic and `container_of` are defined. This reading is
  deliberate: whether `container_of` is defined is debated, and we allow it.
  In C a converted pointer must be correctly aligned for the type it points to
  (6.3.2.3p7): a complete object counts as aligned for every type, as
  `malloc`'s storage is, and the pointer's byte position in it must be a
  multiple of the type's alignment. In C++ such a pointer keeps its value
  (an unspecified one, [expr.static.cast]p13). A character access reads and
  writes a byte of an integer, floating or `bool` object (little-endian); a
  character store or a byte-wise `memcpy` / `memset` that leaves a `bool` or
  floating object with bytes that are no value of its type (a byte other than
  0 or 1, a NaN's bit pattern) leaves them there, and only a read of the
  object as its type is undefined (6.2.6.1p5), or for a NaN not modelled.
  The bytes of pointers, of NaNs the program computes, of padding and of
  indeterminate objects are not modelled (undefined). A pointer converted to
  a pointer to a structure designates the object of that type that it
  starts, or that starts it (6.7.2.1p15), and so does a member access.
  Pointers into one complete object compare by address (C11 6.5.9p6,
  6.5.8p5): a structure and its first member, an array and its element 0, the
  members of a union, one past an object and the object after it compare
  equal, and relational comparisons follow addresses; pointers into different
  objects compare unequal, and their relational comparison is undefined. A
  structure whose members include the types of the objects it covers reads
  and writes them member by member (6.5p7's aggregate clause: `*(P *)&s.a = p`
  with `P` a structure of two ints writes `s.a` and `s.b`), and a member
  access through a pointer to it places the member by bytes; an access
  through a bit-field so placed has the field's declared type, whatever its
  storage unit (CHANGES_bytes.md). Likewise a vector (`!cir.vector<N x T>`,
  the array type `T[N]`) or a complex value read or written through a pointer
  to an object of another type, such as an element of a `T` array or a
  structure of `T` members, reads or writes the objects at its bytes element by
  element: `*(v4sf *)&a[4] = w` writes `a[4]` to `a[7]` (CHANGES_vecstore.md).
* **Conversions between pointers and integers** (C11 6.3.2.3p5, p6) use
  flat addresses, as GCC and Clang do: block `b` starts at `(b + 1) · 2^32`
  (`2^20` for 4-byte pointers), so objects never touch and every object is
  aligned far beyond its type, and a pointer into it adds the byte offset of
  its path; functions have addresses of their own. A pointer to an object
  whose lifetime has ended has an indeterminate value (6.2.4p2): converting
  it to an integer is undefined ("conversion of an invalid pointer"), as
  are comparing it and arithmetic on it. An integer converts to the pointer
  into the live object whose range, one past its end included, holds it,
  so a round trip through `uintptr_t` gives back a pointer to the object
  (7.20.1.4p1; GCC: "the resulting pointer must reference the same object
  as the original pointer"), also after integer arithmetic within the
  object (tags in the low bits, `container_of`). Every live object
  counts, also one whose address the program never converted to an integer
  (PNVI-ae-udi, the provenance model proposed for C, counts only objects
  whose address was exposed): an integer reaches such an object only from
  about 2^32 bytes away or as a constant, which no program written for a
  native layout computes, so no test case covers it. Any other integer,
  e.g. `(char *) 1` or the address of an object that has died (at the exit
  of its scope, by a `longjmp` or a throw out of its frame, by `free` or
  `realloc`), converts to a pointer that compares by its address and
  designates no object: an access through it is undefined, as is its
  relational comparison and arithmetic. Block ids are not reused, so a
  later object never gets the address of one that has died, as it may
  natively. Member function pointers work as the Itanium C++ ABI lays them
  out: a function's address as an integer (or 1 plus a virtual function's
  offset in the vtable) and the adjustment of `this`, which moves as a
  `void *` (GNU C: arithmetic on `void *` counts bytes) before the vtable
  slot is read through the vptr, moved by whole slots.
* **Unions** hold one active member, the one last stored, whichever pointer
  the store went through (C11 6.5.2.3p3, footnote 95); forming a pointer to
  a member activates it too, except in a const object that holds a value (a
  read-only block, which only its initialization writes), where a store
  through another member that reinterprets the held one is undefined like any
  modification (6.7.3p6). A member that becomes active, or is read, while
  indeterminate takes the active member's bytes: a scalar of the same type at
  the same offset keeps its value (pointers included), one of the same size is
  reinterpreted exactly (integers of one width, an integer and a float of its
  width except NaN bit patterns, floats of one kind, a `bool` and a
  character-sized integer, arrays of one integer type and length), and any
  other scalar is composed from the bytes, little-endian,
  as character accesses read them (6.5p7): a narrower member or array element,
  the halves of a wider scalar, a scalar stored byte by byte through a
  character array member. So the common initial sequence of structs reads
  through either struct (6.5.2.3p6), a struct's first member through a scalar
  member, a bit-field unit stored after another member keeps that member's
  other bits, and a character access through a pointer into another member
  reads and writes the stored bytes. A byte the active member does not hold (a
  larger member than the one stored) stays indeterminate. A `bool` byte other
  than 0 / 1 (a trap representation) and a NaN pattern are kept as stored: an
  integer member of their size and character accesses read them, while reading
  them as `bool` is undefined and as a float is not modelled (undefined from
  cirrun). C++ modules: a union member read reinterprets the
  active member's bytes, as GCC and Clang document; ISO C++ leaves it undefined
  ([class.union], [basic.life]p7); the common initial sequence is exempt in
  both. A union with tail padding (CIR's `padding = {…}`) has the size of its
  most aligned member plus the padding. Static storage that the module defines
  is zero-initialised, unions by their first member. A global the module only
  declares (defined in another translation unit or a library) has no value in
  it: a read or a
  write is undefined ("external object without a model"; a constant one has
  a read-only block that is not alive: "invalid memory read"), except for
  the C library's objects that are modelled (the standard streams, glibc's
  `__libc_single_threaded`, getopt's `optind` and `opterr`, 1 at the start,
  libm's `signgam`, 0 until `lgamma` stores a sign in it, the fundamental
  types' typeinfo objects) and the
  C++ standard stream objects (`std::cout`, `std::cerr`, `std::clog`,
  `std::cin` and the wide ones, libc++'s and libstdc++'s), which are live
  objects of indeterminate value: the stream models take them, a read of a
  member is undefined. `cir2lean --link` gives such a global its definition
  from the unit that has it.
* **Bit-fields** are read and written in their storage unit
  (`cir.get_bitfield`/`cir.set_bitfield`, with size, offset and signedness
  from the bit-field info, volatile or not): an integer, or, when the unit's
  width is not that of an integer type (packed structs, wide fields), an
  array of bytes `!cir.array<!u8i x N>` whose bits are numbered
  little-endian across the bytes. Reads sign- or zero-extend (a `bool`
  bit-field reads as a `bool`); a read is undefined when the unit, or a byte
  of it, is indeterminate. Writes keep the other bits; those of a unit that
  was never written read as 0, where C++ leaves them indeterminate. A
  zero-width bit-field (`int : 0`) is a member without storage.
* **Floating point** values are Lean `Float`s (IEEE binary64; `float`
  values are kept rounded to binary32). Arithmetic, `sqrt` and conversions
  from integers use Lean's logical `Float` model; comparisons, conversions to
  integers (truncating; undefined out of range), `floor`/`ceil`/`round`/
  `trunc`/`rint`/`nearbyint`/`fmod`, rounding to `float`, `cir.is_fp_class`
  (LLVM's classes, `fcNegative` and `fcPositive` included) and `cir.signbit` are computed
  exactly from the bits (`CIR/Std/Float.lean`). All of it reduces in the
  kernel.
* **Complex numbers.** `!cir.complex<T>` is the type `T[2]`, real part
  first (C11 6.2.5p13: the representation and alignment of an array of two
  elements of the real type), so complex objects are arrays in memory and a
  complex value is `.arr [re, im]`. `cir.complex.create`, `real`, `imag`,
  `real_ptr`/`imag_ptr` (the addresses of elements 0 and 1), `add`/`sub`
  (integer parts wrap, as Clang's code does) and `fadd`/`fsub` (each part
  IEEE), `cir.cmp eq`/`ne` (both parts equal) and `#cir.const_complex`.
  Clang's CIR spells the rest with scalar operations (negation, the
  conjugate, conversions, integer multiplication and division, floating
  multiplication, which calls `__muldc3` only when both parts come out NaN)
  and calls the runtime library for floating division (`__divdc3`).
* **Vectors** (GNU `vector_size`). `!cir.vector<N x T>` is the type `T[N]`
  and a vector value `.arr xs`: `#cir.const_vector`, `cir.vec.create`,
  `splat`, `extract` and `insert` (undefined at an index outside the
  vector), `shuffle` (an index of -1 gives an indeterminate element),
  `ternary` (a nonzero condition element selects the first operand's),
  `cir.vec.cmp` (-1 or 0 in the result's element type). The
  integer, floating, unary, shift, `cir.fmuladd` and cast operations of a
  vector type act element by element, integer elements wrapping, left shifts
  included (vector arithmetic carries no overflow flags; a division by a zero
  element and an out-of-range shift count are undefined, as for scalars). A `bitcast` between
  vector types, or between a vector and a scalar of its size (`long long`,
  `__int128`, `unsigned`, ...), reinterprets the value's bytes,
  little-endian; an element whose bit pattern is a NaN's, or whose bytes
  come from a NaN or an indeterminate value, is indeterminate (`Float` has a
  single NaN), so only its use is undefined. GCC's manual (Using Vector
  Instructions through Built-in Functions) says "It is possible to cast from
  one vector type to another, provided they are of the same size (in fact,
  you can also cast vectors to and from other data types of the same
  size)". It is a conversion of values, not an access, so the byte-view
  rule of memory is not involved. A pointer to a vector converted to a
  pointer to its element type designates element 0 and its strides count
  the elements, as for any array object; conversely a vector read or written
  through a pointer to an element of a `T` array, or to a structure of `T`
  members, reads or writes the objects at its bytes (see the byte-level
  access bullet). A record lays out a vector member, or an array of vectors,
  as LLVM does, at a multiple of the vector's size rounded up to a power of
  two (`RecordDecl.vecAligns`: CIR's record types hold no padding for it).
  A vector load or store whose stated alignment (`align(N)`, N bytes for
  `vector_size(N)` unless a typedef lowers it) exceeds its element's is
  undefined through a pointer not aligned to N (`Op.alignCheck`): such a
  pointer comes from a conversion that C leaves undefined (6.3.2.3p7) and C++
  unspecified, and the access, an aligned vector move, faults natively. A
  conversion to a misaligned pointer to a vector type that is not used is not
  caught (CIR's types do not show a typedef's alignment, so the conversion
  cannot tell `v4sf *` from a pointer to a vector typedef aligned as its
  element), nor is a three-element vector padded to four. Of the target's
  intrinsics (`cir.call_llvm_intrinsic`), x86's PACKSSDW, PSLLW and PSRLW by
  an immediate count, MAXPS and MOVMSKPS are modelled as the instructions
  compute (`Std.x86Intrinsic`: MAXPS gives its second operand for a NaN in
  either and for two zeros; the sign of a NaN element, which MOVMSKPS reads,
  is not modelled); the others are not.
* **Control.** `cir.if`, `cir.ternary`, `cir.switch`/`cir.case`
  (fall-through), `break`/`continue`/`return` through nested scopes and
  cleanups, unstructured blocks (`cir.br`, `cir.brcond`) inside a region, and
  `goto`/labels: `cir.goto` leaves the enclosing loops and scopes like
  `break` (running their cleanups) up to the region that holds the label.
  GNU computed goto: `&&l` (`cir.block_address`, `#cir.block_addr_info`) is
  a `Ptr.label` value that can be compared and stored, and
  `cir.indirect_goto` continues like `cir.goto` at the label it designates;
  an indirect goto to any other pointer, or to a label of another function,
  and an access through a label address are undefined. A C function that
  reaches the closing brace of a non-void body returns the indeterminate
  value `.undef`, so only a use of the result is undefined (C11 6.9.1p12: a
  store, arithmetic, a comparison or test, passing it on or returning it):
  the frontend marks CIRGen's load of the `__retval` slot at a `cir.return`
  as `Op.retLoad` where it cannot show a store to the slot on every path
  (`CIR/Frontend/Retval.lean`). A structure or union result is `.undef` as a
  whole, and any store of it is undefined (initializing or assigning an
  object, an argument, a member access, a return), but the store CIRGen
  makes of a discarded one into its `agg.tmp` temporary, which the frontend
  drops. C++ has a `cir.trap` there, and `main` returns 0 (C11 5.1.2.2.3:
  CIRGen sets its slot at entry).
* **Program start and termination.** Before the entry the global
  constructors run (`cir.global_ctors`: `constructor(p)` functions and the
  dynamic initialization of C++ globals, by priority). `exit(n)` (also
  `_Exit`, `quick_exit`) ends the program with status `n` (`Exit.halt n`): it
  leaves every scope, loop and call at once, runs no cleanup (C++ destroys no
  automatic objects on `exit`) and no `catch` stops it, and it ends the
  lifetime of no automatic object (C11 7.22.4.4): their blocks stay alive for
  the exit sequence. After a return from the entry (whose automatic objects
  have ended) and at `exit`, the exit sequence runs
  (`CIR/Semantics/Program.lean`): the `atexit` / `__cxa_atexit` handlers, the
  last registered first, those a handler registers included (C11 7.22.4.4p3),
  then the `destructor(p)` functions; the destructor of an object of static
  storage duration, registered by `__cxa_atexit`, ends the object's lifetime
  (C++ [basic.start.term]p1): a later handler (one registered before the
  object's construction) or destructor that uses it is undefined
  ([basic.life]p7); `_Exit` and
  `quick_exit` skip it, and `quick_exit` runs the `at_quick_exit` handlers
  instead, the last registered first (C11 7.22.4.7). `Returns` counts an exit
  as no return
  (`Calls.not_returns`), so a proved specification also shows that the
  function does not call `exit`; a path that does is specified with `Calls`
  (`Examples/Exits.lean`).
* **Non-local jumps.** The parser makes each call of `setjmp` an `Op.setjmp`
  that holds the rest of its block, and of the blocks of the statement
  scopes around it (C11 7.13.1.1p4 allows `setjmp` only as a whole
  controlling expression, also compared with an integer constant or under
  `!`, or as an expression statement; elsewhere it is undefined, p5). The
  rest runs with `setjmp` returning 0, and again with the value of each
  `longjmp` back to that invocation (1 for 0, 7.13.2.1p4), which leaves
  scopes, loops and calls like `exit` (`Exit.longjmp`, no cleanup, no
  `catch`). The function's automatic objects that are not volatile and
  changed between the `setjmp` and the `longjmp` are then indeterminate
  (7.13.2.1p3): changed means stored into, the same value or a value later
  restored included, or holding another value. In a module with a `setjmp`
  (and in the units linked with it), every function notes its stores, which
  the live `setjmp` invocations holding the object record (through a registry
  of the live invocations), so a callee's store counts wherever its pointer
  came from, and a pointer passed to a callee that only reads through it does
  not; so do the stores of the `sscanf`, `scanf` and `strto*` models into the
  program's objects (another library function's store is seen only when it
  changes the value). CIR types no object volatile, only accesses, so an
  object, or a member of a structure, is volatile when its own accesses in the
  function are all `volatile`, or when only `volatile` accesses through other
  pointers reach it, a callee's included (`*(volatile int *)&x` with `x` read
  plainly elsewhere leaves `x` non-volatile). A `setjmp` whose block
  branches to another block (into a label) has its context checked too, and
  returns once: a `longjmp` back to it is not modelled (undefined). A
  `longjmp` to a `setjmp` whose function has returned is undefined
  (7.13.2.1p2), and so, in C++, is one that skips a non-trivial destructor
  ([csetjmp.syn]p2). Not modelled (reported as undefined): a `setjmp` in a
  loop condition jumped back to from the loop body; a `longjmp` after the
  `if` branch, loop iteration, `try` block or cleanup scope that holds its
  `setjmp` was left. GCC's
  `__builtin_setjmp` and `__builtin_longjmp` (`cir.eh.setjmp`,
  `cir.eh.longjmp`) work in the same way, with the value 1 as GCC requires.
  Their buffer, an array of five or more pointers or `intptr_t`s (as GCC
  declares it; a shorter one is undefined), holds the invocation's token in
  its second word, where GCC keeps the resume address; the frame address and
  the stack pointer that CIR stores in the first and third words are not
  stored (the semantics needs neither, and has no model of the frame address:
  `__builtin_frame_address` is not modelled). GCC's manual allows a
  `__builtin_longjmp` only in a function that the function calling
  `__builtin_setjmp` calls: one to that function's own buffer is undefined, and
  one to a buffer that a caller set, in a function that also calls
  `__builtin_setjmp` (a handler re-raising), is not modelled (reported as
  undefined). Nor is the rule that the builtins and the library functions are
  not interchangeable: a token records no pair, so `longjmp` to a buffer of
  `__builtin_setjmp`, or the reverse, jumps.
* **Exceptions.** `cir.throw`, `cir.try` with typed and catch-all handlers
  (a parameter by value, by reference or by pointer, of the thrown type, or
  by pointer through the conversions of C++ [except.handle]p3 that keep the
  pointer: a qualification conversion of the pointee, to `void *`, a function
  pointer conversion, and a `std::nullptr_t` as a null pointer; a pointer and
  a type that is no pointer never match, nor do unrelated pointers; matching
  through a class hierarchy, a multi-level qualification conversion and a
  pointer to member catching `std::nullptr_t` are not modelled),
  `cir.resume`, `noexcept` (an escaping exception is undefined), and cleanups
  on the exceptional path. `throw;` in a handler's own code rethrows the
  exception being handled (the same object); a `throw;` elsewhere, e.g. in a
  function called from a handler, is not modelled.
* **Calls.** Direct calls, calls through function pointers, library models,
  and virtual calls. A vptr holds `Ptr.vtable vt i k` (slot `k` of array `i`
  of the vtable global `vt`). A virtual call reads the slot from the vtable's
  initializer in the module, so proofs need no assumption about vtable memory;
  so do reads of the slots before the address point (the arithmetic on a vptr
  moves over whole slots): the virtual base offsets, the offset to the top and
  the `typeinfo`. The overrider receives the derived object as `this`; an
  overrider reached through a non-primary or a virtual base is called through
  a thunk, which receives the base subobject and adjusts the pointer itself.
  In a class with virtual bases, the base-object constructors and destructors
  set the vptrs from the VTT (`cir.vtt.address_point`), whose entries are
  vptr values, those of construction vtables among them. A zeroed vptr is a
  null pointer, through which a virtual call or a read of the vtable is
  undefined: value-initialization zeroes a polymorphic object before its
  constructor stores the vptr (also through `memset`), as does the
  zero-initialization of static storage before a global's constructor runs.
  The C++ standard stream objects, which a module only declares (the library
  constructs them), are live objects of indeterminate value, so a virtual
  call through one is undefined; any other global with a vptr that a module
  only declares has no value in it at all.
  `cir.vtable.get_vptr` designates the vptr of the object at the pointer's
  location, whatever the pointer's type: a virtual base's vptr is set through
  a pointer of the derived class's type. A function alias
  (`cir.func @f(…) alias(@g)`: Clang's
  complete-object constructor or destructor, C1 or D1, of a class without
  virtual bases defined out of line, which stands for the base-object one,
  C2 or D2, in vtables too; `__attribute__((alias("g")))`) runs the function
  its aliases end at, with that function's body or model, and has its
  address; one declared with another type than that function is no other
  name of it, and a call of it is undefined (C11 6.5.2.2p9). A global alias
  (`cir.global @a alias(@g)`) names the object of its target. The frontend
  resolves aliases when it loads a module (and again when it links units),
  and a cycle of them is an error. A parameter by value of a class that is non-trivial
  for calls (the module has a copy or move constructor or a destructor of it)
  is one object, the caller's temporary, which the callee uses in place and
  the caller destroys at the end of the full expression (C++ [expr.call]p7,
  [class.temporary]p3; Itanium): the frontend makes such a parameter a
  pointer that replaces its slot, and each call passes the temporary its
  argument was loaded from; any other argument of such a class is not
  modelled, never a silent copy. Trivially copyable classes keep the value
  copy. A result by value of such a class is one object too, the caller's,
  which the callee's return statement initializes (C++
  [dcl.init.general]p16.6.1, [stmt.return]p2; Itanium passes its address):
  a function returning one gets a hidden parameter after its named ones, a
  pointer to the caller's object, which replaces its return slot, and
  returns nothing; each call passes the object its result was stored into.
  A return of anything but a load of the slot, and a call whose result is
  used otherwise than by that store, are not modelled (CHANGES_retslot.md).
  A class counts as non-trivial for calls only through the copy or move
  constructors and destructors the module emits: one whose user copy
  constructor is never emitted (elided) and which has no destructor keeps
  the value copy, a labelled gap (CHANGES_retslot.md, Limits).
  An object's lifetime ends when its destructor call starts (C++
  [basic.life]p1): when a destructor with a body returns (ClangIR marks
  every variant, D0, D1, D2 with or without a VTT, their aliases and
  thunks, as `cxx_dtor`), the object it ran on, a complete object or a
  subobject, automatic, a temporary, a by-value parameter, const or on the
  heap, has a fresh object's value again (its scalars indeterminate), so
  reading it is undefined ([basic.life]p7); its storage stays, and a
  placement new may reuse it ([basic.life]p8), before the destructor at the
  end of its scope runs on the new object. The end of a lifetime is no
  store by the program, so a read-only block ends too. Const semantics do
  not apply to an object under construction or destruction ([class.ctor],
  [class.dtor]), and no const class object that a constructor or destructor
  writes is read-only: in C++ a const class object is a plain block, and
  ClangIR marks a class global constant only when it is constant-initialized
  and its destruction is trivial or constant, so that neither runs on it.
  An explicit destructor call whose body writes such a global is reported as
  a modification of a const object; the program is undefined anyway once the
  destructor call at its end finds no object there ([basic.life]p9), unless
  it ends by `quick_exit` or `_Exit`. A library model's destructor keeps its
  own end state. Not detected: a write to a destroyed object, a call of its
  member functions, a second destructor call that does not read it, a new
  object in the storage of a destroyed const object ([basic.life]p10), and
  the end of a temporary without a destructor: ClangIR marks no end of its
  full expression (its `ref.tmp` alloca is at the function's entry), so it
  lives to the end of the function (a C structure with an array member
  returned by a call, C11 6.2.4p8, its modification too; an assigned
  `std::initializer_list`'s backing array).
* **Dynamic allocation.** `operator new` returns untyped heap storage; its
  first cast to `T*` gives it the type `T`, or `T[n]` when it holds n > 1 of
  them (the pointer then designates element 0), so a constructor can
  initialize the members. A pointer to element 0 of an array of class
  objects converted to a pointer to the array's type designates the array,
  and a pointer to a lone object converted to `T(*)[1]` decays to that
  object: `new T[n]` of a class with a constructor, which CIR spells as such a
  conversion, a decay and a loop of constructor calls, constructs the elements
  (CHANGES_arrnew.md, CHANGES_arrfix.md). An array of scalars keeps the
  element pointer, so a vector access over one stays element by element. The array
  cookie of a class with a non-trivial destructor (the element count before
  the elements) is not modelled.

## Trust base

What a proof relies on, beyond Lean's kernel:

1. **The semantics**: `CIR/Semantics/*`, `CIR/Memory.lean`, `CIR/Value.lean`.
   It is checked against native execution by a differential test
   (`tests/difftest/run.sh`, 156 cases across arithmetic, control flow,
   `goto`, RAII, exceptions, classes, virtual dispatch, vectors, strings,
   bit-fields, unions, builtins, floating point, atomics, varargs and the C
   library). 155 match native execution and none disagree. The other one uses the reference returned by
   `emplace_back`, which is not modelled; the semantics reports it as
   undefined. Program termination is compared by exit status
   (`MODE=status CASES=exit_cases.txt`): `exit`, `_Exit` and `quick_exit`
   from `main`, nested calls, loops, loop conditions, `switch`, `try` blocks
   and destructors, against returns from `main`, and the exit sequence
   (handlers, static destructors, `exit` from a constructor). Separate case
   files check constructors and the exit order (`startup_cases.txt`),
   builtins, variable-length arrays, `va_copy`, `strdup` and `getchar`
   (`builtins_cases.txt`), `setjmp`/`longjmp`, with their undefined uses and the cases
   not modelled labelled (`sjlj_cases.txt`), the life of a `va_list`, the argument
   types of `printf` conversions and negative VLA sizes (`vafmt_cases.txt`),
   the `v*printf` functions, a `va_list` after them and `scanf` on the
   empty standard input (`vprintf_cases.txt`), function aliases:
   constructors and destructors, in vtables too, and
   `__attribute__((alias))` (`alias_cases.txt`), virtual inheritance:
   VTTs, construction vtables, virtual base offsets and thunks
   (`vbase_cases.txt`), the globals a program only declares
   (`externglob_cases.txt`), and the findings of an audit (rog's cases and
   more) of `setjmp`/`longjmp` (`auditsj_cases.txt`), of `va_list` and
   `printf` (`auditva_cases.txt`) and of aliases of globals and mistyped
   aliases (`audital_cases.txt`). The models of
   libevent are checked against libevent 2.1.12's static library (`libev_cases.txt`, built with
   the `DT_CFLAGS`/`DT_LIBS` hook of `run.sh`), those of POSIX threads in `pthr_cases.txt`, and
   scheduling, `errno`, `strerror_r`, `time` and `ctime_r`, with `errno` after the C library
   models that set it, in `t2models_cases.txt` (its environment cases labelled).
2. **The frontend** (`CIR/Frontend/`: lexer, parser, emitter), which turns
   CIR text into the AST. Its output can be read in `Gen/*.lean`.
3. **The library models** and their recognition by name and signature
   (`CIR/Model.lean`, `CIR/Frontend/Recognize.lean`, `CIR/Std/Models.lean`).
   A function is modelled only if both its demangled name and its CIR signature
   match, and never when it has internal linkage and a body (a `static`
   function of the program, even one named like a library function). The
   names of libevent and POSIX (threads, scheduling, `strerror_r`) are not
   reserved (C11 7.1.3 reserves the C library's), so their models attach only
   to a declaration without a body, as `__errno_location`'s does: a program's
   own `evbuffer_new` runs its body.
   Libraries outside the C and C++ standard libraries (libevent 2.1, POSIX
   threads, scheduling and time) are modelled from their documentation and,
   where it is silent, their source (libevent 2.1.12-stable) and what glibc
   and Linux do. Where a result depends on the environment of the run rather
   than on the arguments, the models assume one environment
   (`Std.World.current`): every allocation succeeds (`malloc`, `calloc`,
   `operator new`, `strdup`, and libevent's allocations in
   `evhttp_add_header`, `evbuffer_new` and `evbuffer_add`); the program runs
   in one thread, whose `pthread_t` is 1 (`pthread_self`) and which may use
   the real-time scheduling policies (`pthread_setschedparam`,
   `World.rtPrivileged`); glibc's `__libc_single_threaded` is 1, its value in
   a single-threaded process (cirlean runs no threads); getopt's `optind` and
   `opterr` are 1 and libm's `signgam` is 0 when a program starts, glibc's
   initial values; the clock reads the Epoch, 1970-01-01 00:00:00 UTC (`time`,
   `World.now`); and local time is UTC (`ctime_r`, `World.tzOffset`). Standard
   input is empty, and `main(int)` receives `argc` = 1 (`main(int, char **)`
   also `argv` = `{"prog", NULL}`), what the runner's harness passes and what
   `cirrun` gives a `main` run without arguments (C11 5.1.2.2.1 allows
   `main(int)` as an implementation-defined form; GCC and glibc pass `argc`).
4. **Clang's CIR generation**: C++ semantics that Clang resolves before CIR
   (overload resolution, implicit conversions, the order of destructor calls)
   is trusted.

All tactics produce kernel-checked proofs; none of them is trusted.

**Mutation testing** checks that the specifications are strong enough to
notice bugs. `tools/mutate.py EXAMPLE` plants one bug at a time in the C++
source (flipped comparisons, `+`/`-`, off-by-one constants, `&&`/`||`, ...),
regenerates the CIR and the Lean module, and re-checks the unchanged proof
file. On the ten example files (149 mutants, three of which do not compile),
every mutant of code that a theorem covers was killed (134), except 7
equivalent mutants that compute the same values (`x < 0` to `x <= 0` in
`abs_val`, `a > b` to `a >= b` in `max2`, ...). The 5 survivors outside these
are in `sum_to`, which has no theorem.

Known modelling limits (each is either undefined behaviour, so proofs about
it fail safely, or noted here):

* floating-point values are Lean `Float`s (IEEE double; `float` results are
  rounded to single precision, `long double` is computed as double);
  `fmuladd` is evaluated unfused;
* `operator new` never fails (no `bad_alloc`);
* a catch clause matches an exception of exactly its type; matching against
  a different class type (through a base class) is undefined;
* operations the frontend does not know become `Op.unknown`, which is
  undefined: a proof that reaches one fails;
* inline assembly is undefined, except an empty template (or `nop`), which
  leaves its operands as they are: without outputs (`asm volatile("" ::: "memory")`,
  a compiler barrier, or inputs only, in registers or in memory) it is a no-op;
  an output tied to an input of its type (`asm("" : "+r"(x))`,
  `asm("" : "=r"(y) : "0"(x))`, and through memory `"+g"(x)`, `"=g"(y) : "0"(x)`)
  gets that input's value, and a memory output that is not tied (`"+m"(x)`)
  keeps its own; and the template `movl %0, %1` of a 32-bit register input and
  a memory input stores the first into the second. An input of another type
  than its output (an `int` given the bytes of a pointer) stays undefined;
* object representation (bytes, `reinterpret_cast`, a floating union member
  over a NaN pattern, a union member over bytes the active member does not
  hold) is not modelled; such accesses are undefined;
* the objects that a module only declares and that are not modelled (`environ`,
  glibc's `program_invocation_name`, a global of another unit that is not
  linked in) are undefined to read or write, and so are the members of the C++
  standard stream objects (see Semantics);
* `dynamic_cast` is not modelled (the typeinfo objects are record constants:
  `typeid(T) == typeid(U)` compares them, and the `typeid` of a polymorphic
  object is the one its vtable refers to; those of the fundamental types, which
  the C++ runtime library defines, get their library value, an indeterminate
  vptr and the name `_ZTS…`; a typeinfo's name, a pointer to the `_ZTS` array
  object, reads as a string from its element 0);
* the unwritten bits of a bit-field storage unit read as 0 (see Semantics);
* a const-qualified local object (`Op.allocaConst`, a read-only block) is not
  ended when its region exits, since a region exit ends stack blocks only, so
  an access through a pointer to it after its block has been left, also one
  converted from its address as an integer, is not caught
  (`constobj_cases.txt`: `c_scope`; `intptr_cases.txt`: `i_const_scope`),
  unlike for any other local;
* CIR gives `char` and `signed char` one type (`!s8i`), `char8_t` that of
  `unsigned char` (`!u8i`), and `long` and `long long` one type (`!s64i`), in
  objects, members, globals, casts and accesses alike (only the mangled names
  of functions keep their parameters' types), so what tells them apart is not
  checked: C++'s aliasing rule, which allows `char`, `unsigned char` and
  `std::byte` but not `signed char` or `char8_t` ([basic.lval]p11; C allows
  every character type), and a `long long` passed to `%ld` or read by
  `va_arg(ap, long)` (and `long` for `%lld`);
* a `printf`-family call through a function pointer is not checked against
  its format: the callee is known only when the call runs, and the arguments
  reach it as values;
* a pointer to an object whose lifetime has ended is true in a condition
  (`if (p)`, `cir.cast(ptr_to_bool)`), although comparing it with null is
  undefined ("comparison of an invalid pointer", 6.2.4p2): a known
  inconsistency (`intptr_cases.txt`: `i_bool_dead_local`).

## Code map

| path | content |
|---|---|
| `CIR/Syntax.lean`, `CIR/Module.lean` | AST of CIR: types, records, ops, regions, modules |
| `CIR/Value.lean`, `CIR/Memory.lean` | values, pointers, memory, pointer arithmetic |
| `CIR/Semantics/` | interpreter (`Eval.lean`), arithmetic and loads/stores (`Basic.lean`), initial memory |
| `CIR/Model.lean`, `CIR/Std/Models.lean` | library models |
| `CIR/Frontend/` | CIR parser, Lean emitter, library recognition |
| `CIR/Logic/` | `Returns`/`Calls`, call and frame rules (`WP.lean`), symbolic execution lemmas (`Exec.lean`), loop rules and loop invariants (`Loops.lean`) |
| `CIR/Tactic/` | `cir_vcg` (`VCG.lean`), `cir_loop` (`Loop.lean`), calls and specifications (`Call.lean`), lookup simprocs, simp sets |
| `CIR/Lib/List.lean` | `grind` lemmas for loops over lists (prefix sums, counting, search) |
| `Cir2Lean.lean`, `CirRun.lean`, `CirScan.lean` | the executables |
| `tools/` | `cirinv_v5.py` (automatic proofs and witnesses), `cirinv_batch_v2.py`, `cirinv_contracts.py`, `mutate.py` |
| `Examples/` | verified examples |
| `tests/difftest/` | differential testing against native execution |

## Building

```sh
lake build            # the library (Lean 4 v4.35.0, no Mathlib)
lake build cir2lean cirrun cirscan
lake env lean Examples/Vectors.lean
```

## Writing proofs: tips

* Leftover goals are pure statements about the program's values. Prove them
  with `omega`/`grind`, or add a lemma to `CIR/Lib` tagged for `grind`.
* State facts about containers through the list of elements `xs`
  (`.vec g (xs.map .int)`). Overflow-freedom of sums is a precondition such as
  `Lib.PrefixSumsIn lo hi xs`.
* Give every function a `@[cir_spec]`. A caller then never depends on its
  callees' bodies, and a change to a callee needs only the callee's proof to
  be checked again.
* For unsigned loop counters, name the counter as a `Nat` and write the
  invariant with `xs.take i`, `xs[i]`, ...
