# StrictTS bridge (an agent): status 2026-10-24, StrictTS pinned at a15926a (branch strictts-a15926a, checked 02:50 UTC)

All 23 TS files compile cleanly against StrictTS a15926a: the 7 bridge files, the 7 demos and the 9 generated inputs below. They pass `lake build` of the TS targets, and `Bridge/Registry.lean` and `Demo/XLang/ReverseBits.lean`, which import the TS loop shapes, build too. Each bridge and demo file also elaborates with `scripts/lean1.sh` from the repository root. There are no warnings, no `sorry` and no `bv_decide`. Every theorem of the TS demos and of the bridge passes `#print axioms` with `[propext, Classical.choice, Quot.sound]` or a subset; 227 theorems were enumerated, generated equation lemmas included. Times are wall-clock, one thread (`lean1.sh`), import time included.

**Pin** (re-pinned 2026-10-24 from 5b0e687): `../equivlean_work/vendor/strictts-a15926a`, a clone of `~/strictts` checked out at a15926a. Its `lake build StrictTS` takes 40 jobs and 71 s with 4 threads (log `../equivlean_work/logs/build_strictts_a15926a.log`). The `strictts` entry in `lakefile.toml`, `lake-manifest.json` and `scripts/lean1.sh` points at it.

Changes in StrictTS since 5b0e687, and what each one meant here:
- New `Ty`/`Val` cases (`ext`, `dict`, `dyn`), `Expr.extern`/`externAsync`, the world's external oracle `ext`/`extIdx` with `EVal` answers, and `dynStr` panicking on objects with their own `toString`/`valueOf`:
  - The bridge has no exhaustive match over `Ty`, `Val`, `Expr` or `World`, so no case was missing.
  - The interpreter's mutual `partial_fixpoint` still has its 26 components in the same order. So `ts_extract_mutual_fixpoint`, the component projections in `Terminates.lean` and the verbatim loop-body copies in `Loops.lean` are unchanged; the loop functions themselves did not change.
- New `@[simp, ts_sym]` lemmas, e.g. `Conv.strictEq_num : strictEq .num x y = numEq x.toNum y.toNum`. `PrDiff.contains_equiv` split on `Conv.strictEq Ty.num xs[i] (Val.num v)`, which `ts_sym` now rewrites away. The proof now splits on `Conv.numEq xs[i].toNum v`. The statement is unchanged.
- `ts_auto` is now StrictTS's own automation (`StrictTS.Proof.Auto`). Our per-direction macro had the same name. In a file that imports both, a bare `ts_auto` ran our macro and never StrictTS's tactic (checked; Lean does not fall back to the other parse when the first one fails). Ours is renamed `ts_auto_couple`; `equiv_ts_auto` is unchanged.
- The front end at a15926a regenerates the 9 `Demo/Gen/TS` files byte for byte. `examples/ts/regen.sh` now uses the new pin, with its own scratch copy of the front end, and writes into the repository or worktree that contains the script.
- Not part of a15926a: f64eval (`F64Eval.lean`, `Math.pow` deciding ECMA-262 steps 1-12 itself, `ts_eval`). It is StrictTS fb68b8c, merged to master as b3ab7f9 after a15926a. Between a15926a and master bdd6a08 there is no change to `Core` (`Ty`/`Val`/`Expr`/`World`), only `Lib/Prim`, `Num/F64*`, `Proof/Auto` (one line), `Proof/Eval` and `Proof/F64Eval`.

**Bridge** (`EquivLean/Bridge/TS/`, namespace `EquivLean.TS`)
- `Behaves.lean` (1.1 s): the core `Behaves (Option _)` instance on `JS.exec m w`. Divergence is unsafe; value, thrown error and panic are all outcomes, each paired with the final world.
  - The final world includes the oracle positions (`randIdx`, `nowIdx`, `extIdx`). So `Equiv (· = ·)` requires both sides to make the same number of external calls.
  - The oracle answers by call number, so reordering external calls is not an equivalence whenever an answer or an exception reaches the outcome: an oracle that differs at one position tells the orders apart.
  - `Strict m w` is a second reading where a panic is unsafe (a step outside the modelled fragment). It is Total and Det, with `wp_strict_iff`, `Sim.strict` and `Equiv.strict_of_eq`.
  - `wp_exec_match` (simp) is the bind rule in exactly the `match` shape that `JS.exec_bind` produces. Also: `call`, `sim_some_some`, `sim_some_of_wp`, `sim_some_iff`.
- `Loops.lean` (3.5 s): `loopShape` (while/for), `doShape`, `forOfShape`, `forOfMapShape`, `forOfSetShape`, `forOfStrShape`. Each has a step function returning `.inl` (leave) or `.inr` (continue), plus `stepCls`, and is derived from `.eq_1` through a verbatim `…BodyWith` copy of the loop body.
- `Terminates.lean` (3.3 s, written by an agent): the six `…Terminates` theorems (loop, do, forOf, forOfMap, forOfSet, forOfStr). They come from fixpoint induction on `evalE.mutual = Lean.Order.fix mutF _`. `mutF` is read off the definition by the command `ts_extract_mutual_fixpoint`, which uses `addDecl`; the result is kernel-checked.
- `Obs.lean` (1.2 s):
  - `WorldObs n` compares the console, the heap cells below the caller's `next`, and `OracleIdx`: the same `randIdx`, `nowIdx` and `extIdx`. The oracle positions were added with this pin, because a callee that makes one external call more or fewer shifts every later answer the caller gets. Lemmas: `WorldObs.extIdx_succ`, `WorldObs.extIdx_eq`.
  - `ObsEq` (same completion plus `WorldObs`); `ArrObs n`, equivalence modulo fresh allocation (same caller array, or fresh arrays with equal contents), with `arrObs_of_specs` and `equiv_arrObs_of_runs`; `TSEquivOn` with `tsEquivOn_of_equivOn` (the encoding-level `EquivOn`).
  - Not compared: the asynchronous state (microtask queue, timers, unhandled rejections), as before.
- `Corr.lean` (1.3 s): `NumInt` (`Corr F64 Int`, exact safe-integer arithmetic); `NumU32`/`NumI32` (`Corr F64 (BitVec 32)`, int32 idiom lemmas `bxor_…`, `imul_…`, `shr_zero_…`); `ArrHolds`, `TArrHolds`, `MapHolds`, `MapList`; `arrFilter_pure`.
- `Tactic.lean` (1.8 s):
  - `ts_start` / `equiv_ts`: `sim_iff_wp`, then symbolic execution of both sides; the source becomes `hs`.
  - `ts_lockstep J, R` pairs two TS loops via `wp_loop_rel`; `ts_lockstep_x J, R using sh, tm` pairs a TS loop with another encoding's loop.
  - `ts_step_simp` computes one step of each loop. `evalE_taGet_*` makes typed-array reads executable.

**Demos on real front-end output** (`examples/ts/*.ts` → `Demo/Gen/TS/*.lean`; `examples/ts/regen.sh` reproduces them byte for byte from a scratch copy of the pinned front end). Per-theorem times below were measured inside the file (elaboration plus kernel check); file times include imports.
- (a) `Demo/TS/PrDiff.lean` (13.6 s), PR `pr_old` → `pr_new`. Both results are `Equiv (· = ·)` (same value, exception or panic, and world) for all arrays and worlds with `xs.size < 2^32`, both directions lockstep, no variant, plus `…_strict` corollaries.
  - `sum_equiv` (0.5 s, with `sum_step` 2.1 s): an index `for` loop became `for…of`.
  - `contains_equiv` (8.6 s): an early `return` became flag + `break`.
  - `sumSpec_take_succ` and `take_size` use `[propext, Quot.sound]`.
- `Demo/TS/DoWhile.lean` (7.4 s), `digits_equiv` (6.4 s): `do…while` became `while(true)…break`. It holds for every `number`, NaN included, and `+∞`, where both sides diverge.
- (b) `Demo/TS/FnvXLang.lean` (7.2 s), `fnv_equiv`: TS FNV-1a (`Math.imul`, `Uint8Array`) is `Equiv` to eq-aeneas's real Aeneas `bits.fnv1a32` (`wrapping_mul`, `&[u8]`), given `BytesCorr`.
  - It is a lockstep of the TS `for` against the Aeneas `loop` via `ts_lockstep_x`, in both directions (`fnv_ts_sim_rust` 2.8 s, `fnv_rust_sim_ts` 2.5 s).
  - The leaves are closed by the int32 lemmas, Aeneas `bv` lemmas and omega.
- `Demo/TS/FnvSpec.lean` (1.9 s): `fnv_equiv_spec` chains `fnv_equiv` with eq-aeneas's `fnv1a32_equiv_fnv` through `Equiv.trans`, giving TS ≈ the pure Lean fold `fnv`.
- Fresh allocation, both `Equiv (ArrObs w.next)`, each with a `…_runs_differ` showing plain `=` fails: `Demo/TS/ScaleFresh.lean` (1.6 s, `scale_equiv`, map fusion) and `Demo/TS/FilterLoop.lean` (2.3 s, `doublePositives_equiv`, filter+map became a loop with `push`). Their statements are unchanged, but `ArrObs` now includes the oracle positions; neither function makes an external call.

**AutoCouple**: `Bridge/TS/AutoCouple.lean` (2.5 s) provides `equiv_ts_auto [defs]`, which is `equiv_ts` and then `ts_auto_couple` on each direction: a generated lockstep coupling, or the straight-line closer.
- The coupling: entries are aligned from the bottom of the environment; mutable entries are equal, `const`/unaligned entries keep their loop-entry values; the index-loop counter = the `for…of` index; the worlds are equal. The exit relation is the continuation implication `K₂ o₂ → K₁ o₁`.
- Values of single-constructor types are destructed in the step; this now includes dictionary and external-handle values, but not `unknown` values.
- If it fails, it leaves the goal for `ts_lockstep J, R`.
- `Demo/TS/AutoCouple.lean` (18.6 s) proves `sum_auto` (4.8 s), `contains_auto` (6.2 s) and `digits_auto` (4.0 s) with no coupling written (std axioms).
- It works in a file that also imports `StrictTS.Proof.Auto` (checked).
- **Limitation for CI**: pairing an index loop with a `for…of` needs a hypothesis `size < 2^32` in context, because the model does not bound array lengths. Without it, `equiv_ts_auto` returns the goals unproved.

**Follow-ups (not done)**:
- `ts_summarize`/`ts_callbacks` (`Proof/Summarize.lean`) and StrictTS's `ts_auto` (`Proof/Auto.lean`), now in the pin, as a fold front end before lockstep.
- Registering the `…_spec` lemmas with the core `@[equiv_spec]`/`equiv_call`.
- A demo with external calls (same calls in the same order versus a reordering) and one with `unknown`/dictionary values.
- Re-pin to master bdd6a08 or later for f64eval.

**Gaps**
- Not covered: async CPS loops (`loopA`, …); `ArrObs` for arrays whose elements carry references (now also `dict` and `dyn` elements); a stuttering TS demo. `EquivLean.lean` does not import these modules yet.
- External calls: the world records how many external calls were made, not their arguments. Calls whose answers and errors are both discarded therefore leave no trace beyond `extIdx`. This is a property of StrictTS's world model.
- Pitfalls: typed-array reads have Expr index `.num` while the builtin has `TAKind.elem k`. With Mathlib imported, `2 ^ 32` breaks the omega side conditions (write numerals), and Mathlib `simp` on F64 or `toNat` goals hits kernel deep recursion. `lean1.sh -o` must be run from the repo root. `ts_sym` rewrites `Conv.strictEq` at primitive types to `numEq`/`==`, so split on those forms.

**AutoXLang.lean (2026-10-24, helper; 3.7 s).** `ts_rust_lockstep`, `sim_ts_rust [defs] with [lemmas]` and `equiv_ts_rust` pair a TypeScript `for`/`while` (or `do … while`) loop with an Aeneas `loop`, in either direction, with a generated coupling. The coupling fixes the entry world, gives the entry env in which each paired mutable slot holds the Rust variable as a number (`F64.ofNat x.val` for usize/u8/u16, `F64.ofUint32 x.bv` for u32, `F64.ofInt32 x.bv` for i32), and adds the Rust loop bounds. Slots are paired in declaration order, then in order of first assignment. The exit relation is the implication between the continuations. Each attempt is atomic, with an error listing the couplings tried. The arithmetic of one iteration is given as step lemmas (`with [...]`). `bor_zero_add_ofInt32_ofNat` completes the int32 bridge for `(y + n) | 0`.
- `Demo/TS/AutoFnvXLang.lean` (14.1 s): `fnv_ts_sim_rust`, `fnv_rust_sim_ts` and `fnv_equiv` (the statements of `FnvXLang`) with no coupling written.
- `Demo/TS/AutoPolyHash.lean` (7.8 s): `examples/ts/poly_hash.ts` against `examples/rust/polyhash` (`(Math.imul(h, 31) + b) | 0` against i32 `wrapping_mul`/`wrapping_add`), `poly_equiv` with no coupling written.
- Not covered: `for … of`, loops that write the heap, 64-bit Rust variables, couplings that relate variables to each other.
