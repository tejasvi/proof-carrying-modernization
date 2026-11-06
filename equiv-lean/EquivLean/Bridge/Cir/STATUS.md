# CIR (cirlean) bridge: final report (eq-cir, 2026-10-23; times below on cirlean 0cdae62; on master e9db0a3 = cirlean 87a2905 the integrator rebuilt all, rc=0: EarlyExit 232 s, TwoLoops 217 s, VectorLoop 357 s)
Files, namespace `EquivLean.Cir` (all compile: `scripts/lean1.sh -o`, cwd = repo root, LRUN_AS=134217728):
- `Bridge/Cir/Behaves.lean`: `instBehavesRes : Behaves (Res α) α` (Runs = `ok`; Safe = `∃ a, x = ok a`,
  so `ub`/`div` unsafe), `Total`/`Det`, `@[simp] wp_res : wp x Q ↔ x.holds Q`, `holds_of_wp`,
  `wp_of_holds`, `pholds`, `sim_res_iff`, `sim_res_iff_holds`, `sim_res_res`.
- `Bridge/Cir/Loops.lean`: `loopShape_for/while/do`, `terminates_for/while/do`, tagged
  `@[equiv_loop_shape]`/`@[equiv_loop_term]` (`equiv_loop_auto` finds them). Termination by
  `Lean.Order.fix_induct` on cirlean's 12-function mutual `partial_fixpoint` (functional named by
  `cir_name_functional%`; motive `x ⊑ fix ∧ (x.loop σ = ok r → Acc Next σ) ∧ …`).
- `Bridge/Cir/Obs.lean`: `ObsEq m₀`, `EquivOn Bad ctxNew fNew ctxOld fOld` (promised names),
  `EquivOn.intro`, `EquivOn.changed_subset`, `obsEq_flip`; `ObsEqGen`/`EquivOnGen` (mod generations).
- `Bridge/Cir/Tactic.lean`: `equiv_cir` (Sim / Equiv / `Cir.EquivOn` with `Bad = ¬∃ x…, args = […] ∧ P`),
  `equiv_cir using inv` and `using [inv₁, …]` (loops in sequence, lockstep via `wp_loop_rel`, no
  variant; binders `x` target / `x'` source: int, size_t, range-for iterator). Pieces: `cir_hrun`
  (source runs in a hypothesis with cirlean's simp sets/simprocs/discharger), `cir_loop_pair`
  (cirlean-style frame/slot facts on both sides; loop outcome relation "continuations agree"),
  `cir_pair_step`, `cir_sim_loop(s)`, `cir_obs_close`, `cir_equivOn_intro`. Source of any encoding:
  `equiv_cir_loop (fun x… s₂ => …) using (h₂shape), (h₂term)` (CIR loop in the goal, `wp (L₂ s₂) K₂`
  hypothesis; leaves `cir_init` and the `cir_step` Sim goal with the target's loop-head facts).
Demos on real clang -fclangir + cir2lean output (`examples/cir/*.cpp`, `examples/cir/gen.sh`):
- (a) `Demo/Cir/StraightLine.lean`: `clamp_equiv`, `max3_equiv`, `*_equivOn` (branches vs libc++
  `std::min`/`std::max` models; unconditional).
- (b) `Demo/Cir/LoopRefactor.lean`: `sum_below_equiv`, `sum_below_equivOn` (for vs while).
- (b2) `Demo/Cir/EarlyExit.lean`: `find_first_sim(_rev)`, `find_first_equivOn` (return in loop vs break).
- (b3) `Demo/Cir/VectorLoop.lean`: `vsum_sim(_rev)`, `vsum_equiv` (std::vector index loop vs range-for;
  caller block `.vec g (xs.map .int)`, length < 2^63, int elements; no sum precondition).
- (b4) `Demo/Cir/TwoLoops.lean`: `sum_then_count_sim(_rev)`, `sum_then_count_equiv` (2 loops in sequence).
- (c) `Demo/Cir/BugFix.lean`: `average_equivOn` (Bad = `a + b` overflows; `by equiv_cir`),
  `average_old_ub` (old is UB on every well-typed Bad call), `average_new_spec` (new always safe).
Loop theorems need no overflow precondition (both sides UB at the same iteration). Check times (load ~170,
lean1.sh with autoImplicit=false, `scratch/eq-cir/recompile_all.sh`): Behaves 5 s, Loops 7 s, Obs 8 s, Tactic
18 s; StraightLine 117 s, BugFix 19 s, LoopRefactor 73 s, EarlyExit 200 s, VectorLoop 240 s, TwoLoops 196 s.
`#print axioms` (scratch `t/Axioms.lean`): all 18 demo theorems and `terminates_*` use exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `bv_decide`/native axioms.
Open gaps: lockstep only (loops nested in a loop body, unrolling/stuttering not automated; generic
`equiv_loop_async` sees the CIR shapes but its step goals are manual); loop variables limited to
int/size_t/iterators (not containers modified through a pointer); `EquivOn` demos put ill-typed
calls in `Bad`; loop demos take 1.5–2.5 min per direction (one direction per theorem: a single
`Equiv` with two loop pairs per side exceeded 4M heartbeats); `ObsEqGen` has no demo; `Corr.lean` is
main's (bit vectors; no name clashes with my files).

## Automatic coupling (23:05 UTC, `Bridge/Cir/AutoCouple.lean`, demo `Demo/Cir/AutoCouple.lean`)
Importing `AutoCouple` makes `equiv_cir` (no `using`) couple same-shape loop pairs itself: variables
paired by C name + kind, then position (`x = x'`; `__retval` etc. skipped); entry values of the others
(`r = -1`); 2nd attempt without them; 3rd adds bounds `x ≤ y` for counters compared by `<`/`!=` with an
unmodified variable. Each attempt must close all goals, else the old `equiv_cir` runs (goals open).
Proved with plain `equiv_cir`: LoopRefactor `Equiv` (61–94 s), countBits with an extra guarded branch
(`Sim` in the demo; `Equiv` too in scratch), EarlyExit both directions (318 s, scratch only), `i < n` vs
`i != n` with `0 ≤ n` (`Equiv`, 248 s, scratch only).
Containers (2026-10-24, main): a 4th attempt (attempts 1-3 unchanged) also pairs a range-`for` iterator
by position with a `size_t` index (both element positions, `Nat`) and bounds the paired
counters/iterator positions by the length of each caller vector in context (`it ≤ L.length` from
`m.blocks b = some ⟨_, _, _, .vec g L⟩`), the other variables unconstrained. `Demo/Cir/AutoVector.lean`: VectorLoop's `std::vector` refactor with
no coupling written, both directions and `Equiv` via plain `equiv_cir` (153 s for the file with
`lean1.sh`, one thread; 347 s in a parallel lake build). Several vectors in context: every bound is
added, so the attempt fails when one of them does not hold (then `using` is needed).

## Pointer arguments (2026-10-24, main; `Bridge/Cir/{PtrArgs,PtrLemmas,ValSwap}.lean`, demo `Demo/Cir/PtrArgs.lean`)
Statement: each pointer argument `x` comes with `∀ b p, x = .loc b p → b < m.next` (null, a
function or vtable pointer, or a block of the caller; a block at or above `m.next` is one of the
callee's locals, which two versions allocate differently, so without the bound `equivalent` is false
in cirlean's model). With `PtrArgs` imported, plain `equiv_cir` (also after `cir_equivOn_intro`) takes
the bound (`cir_ptr_intro`, renamed `cirP_ptrN`) and
- splits the pointer where the source first inspects it (`splitPtrVar`, when a load, store, stride
  or comparison would get stuck on it; that step is then redone): null / fn / vtable / `loc b p`
  with `cirH_ltN : b < m.next`, `IsCaller b`, and the block of an earlier pointer (substituted) or a
  new one (`cirH_blkN : m.blocks b = none / some ⟨kind, alive, ty, val⟩`);
- names the source's case splits on caller data `cirH_rdN` (`val.get? p = some v`, the path's last
  step and parent array of `a[i]`, …; the innermost `match`/`if` is split first), which `cir_vcg` uses
  on the target's identical terms;
- `cir_ptr_saturate`: two writes of the source into one caller value at leaf positions it read
  before give the facts of the other order (`Val.set?_swap`; equal positions hold equal values);
- `cir_obs_close` compares the caller blocks written by both calls case by case (`cir_upd_cases`).
Loop pairing (all CIR loop proofs): the target of a paired iteration runs with `cir_vcg_tgt`, which
leaves the `StepRel` leaf to `cir_pair_step` (cirlean's eager fallback spent ~40 s on each such leaf):
rebuild 02:09–02:17Z, LoopRefactor 44 s, EarlyExit 65 s, TwoLoops 82 s, VectorLoop 73 s, AutoEarlyExit
38 s, AutoBound 67 s, AutoCountBits 71 s, AutoCouple 76 s (before: 73–95, 200–277, 196–217, 240–357,
245–317, 307–390, 114–138, 137 s).
Results (plain `equiv_cir`, maxHeartbeats 4M): veriforch's `VOEquiv/{get_or,swap,sum_arr}_b88e74c_018ebeb`
(`equivalent` and `changed_only_where_old_unsafe`; only `import EquivLean.Bridge.Cir.PtrArgs` added)
63 s / 90 s / 229 s, all six `[propext, Classical.choice, Quot.sound]`; `Demo/Cir/PtrArgs.lean` (the same
functions from `examples/cir/p_{old,new}.cpp`, no range hypotheses) 241 s.
Open: records passed by value with pointer fields (veriforch stops them at `unknown`); writes through
pointers that the source did not read first (no `get?` facts for `cir_ptr_saturate`); `sum_arr` spends
its time in 8 source cases per iteration (array element via `.idx`/`.vel`, a non-element pointer at
offset 0, …), each followed by one target run.

## Re-pin to cirlean 88e6008 (2026-10-24, helper cir-repin)
cirlean's typed load changed (60ecdbf): `loadTy` at an `int` type reads an integer outside the type's
range but in the range of its signed/unsigned counterpart as `wrap s w x` (C11 6.5p7), where it was
undefined behaviour before. Every load of an integer whose range the discharger cannot decide now has
a second live branch.
- Pointer mode (`get_or`: open goals, `swap`: > 25 min): a value read from caller memory is unknown,
  and the source split the load's `match ty, v` with `splitMatch`, which generalized the constructor
  discriminant and left `Ty.int true 32 = Ty.int s w` named `cirH_rd…`: the target's `cir_vcg` used it
  as a rewrite rule (its slots got the type `Ty.int s w`), the source's facts stayed in `match` form,
  and the two sides took different branches. Now (`Tactic.lean`): a `Val` that an `if` condition
  inspects (`fitsTy ty v`) is split on its constructor first (`valToSplit?`, `casesVal`), so the
  facts are `inRange …` on the integer read; after `splitMatch`, equations between constructor
  applications are solved by `cases` (`casesCtorEqs`); `cir_leaf` accepts scalar constructors;
  `cir_ptr_saturate` compares two integers read at one position. `load_int_merge_s`/`_u`
  (`PtrLemmas.lean`), added by `cir_ptr_intro` as rewrite rules `cirH_ldS`/`cirH_ldU` of both
  programs, make the in-range and counterpart reads one path with the value `wrap s w x` (`sum_arr`
  forward with `lean1.sh`: 145 s with two paths, 88 s with one; 74 s on 87a2905). `Demo/Cir/PtrArgs`
  with `lean1.sh`, run side by side with the same file on master (87a2905): 410 s against 408 s;
  `Demo/Cir/AutoVector`: 456 s against 368 s.
- `splitPtrVar` splits integer pointers `addr a` too (8d472ce); `ptrValid`, `read?`, `write?` through
  them compute (`PtrLemmas.lean`).
- `AutoCouple`: the vector bound strips `List.map` (`xs.length`, the form cirlean's `cir_elems`
  relates to `∀ x ∈ xs`; `L.length` for `xs.map .int` failed in the reverse direction).
- Hand-written XLang proofs: `Point` and `VecSum` state the C loads' ranges as literal bounds before
  running C (`p.x.val`, `p.y.val`; the elements of `xs`, the slots `s` and `i`), so that
  `inRange_of_bounds` decides the checks; `VecSum`'s post case closes the counterpart branch of the
  load of `s` by `omega`, its `r0` leaf is `assumption` (branch facts renumbered); `ReverseBits`: a
  `simp only [Int.toNat_one, pow_one]` became a no-op (cirlean's `cir_vcg` now reduces `(↑1).toNat`
  and `2 ^ 1`) and is removed.

## Re-pin to cirlean bd8614f (2026-10-25, helper cir-repin)
cirlean bd8614f (the C maintainer session's cJSON pin, 17 commits after 88e6008): list and tree support (`CJTree`, `listPtr`),
second loops in a function, frame closers (`CIR/Tactic/Frame.lean`), and a `cir_disch` with two more
alternatives (`cir_idx_omega`, `cir_hyp_apply`). `cir2lean` is unchanged: `examples/cir/gen.sh` regenerates
`Demo/Gen/Cir` identical up to absolute paths (the committed files are kept).
- API: `CIR.Tactic.cirHyps` returns `Array Term` (a hypothesis shadowed by a later one of the same name is
  passed as the hypothesis itself) and `simpArgs` takes terms. `hypSimpArgs` (`Tactic.lean`) left out `h` by
  `getId`; it now asks `cirHypsExcept` to leave out `h`'s free variable.
- Heartbeats: two loop equivalences proved by plain `equiv_cir`, both directions in one declaration, pass
  4M heartbeats on bd8614f (the discharger's new alternatives run on every failing side condition):
  `Demo/Cir/AutoVector.vsum_equiv_auto` and `Demo/Cir/PtrArgs.sum_arr_equiv` now carry
  `set_option maxHeartbeats 12000000 in`. Nothing else changed in the proofs.
- Build (`lake build`, one thread, LEAN_NUM_THREADS=1): all 46 cirlean-dependent modules (Bridge/Cir 9,
  Bridge 1, Demo/Cir 12, Demo/Gen/Cir 21, Demo/XLang 3). Demo times: LoopRefactor 35 s, TwoLoops 60, EarlyExit
  50, BugFix 20, VectorLoop 37, StraightLine 80, AutoCountBits 74, AutoBound 128, AutoEarlyExit 62, AutoCouple
  128, AutoVector 476, PtrArgs 352; XLang Point 82, ReverseBits 70, VecSum 46. Axioms: all 203 theorems of
  the 46 modules `[propext, Classical.choice, Quot.sound]`.
