# Aeneas (Rust) bridge: status (eq-aeneas, 2026-10-23 22:02 UTC)

Everything is in namespace `EquivLean.Aeneas`. All 30 files (including the C++ ↔ Rust VecSum demo) were rebuilt in dependency order with `scripts/lean1.sh -o` at 22:00 UTC, on cirlean 87a2905: no errors, no `sorry`, about 110 s in total. To rebuild: `../equivlean_work/scratch/eq-aeneas/rebuild.sh`.
**Behaves.lean (2.7 s)**
- Instance `Behaves (Result α) (Except Error α)`: `Runs c o := c = ofExcept o`, `Safe c := ∃ o, c = ofExcept o`. So `Safe` means "not `div`" (`safe_iff_ne_div`), and a panic is an outcome. `Total` and `Det` hold.
- simp lemmas for `wp`: ok/fail/div/pure/lift, `Std.bind` and `>>=`, `ite`/`dite`, massert, ofOption, Slice/Vec `index_usize`, `Vec.push`.
- Aeneas `spec`/`dspec`: `spec_iff_wp`, `wp_of_spec`, `dspec_iff`.
- Checked scalar operations, with both outcomes, derived from Aeneas' definitions:
  - value form (default simp): `wp_{U,I}Scalar_{add,sub,mul,div}_val`, `wp_UScalar_rem_val`, `wp_IScalar_neg_val`;
  - exact bit-vector form: `wp_{U,I}Scalar_{add,sub,mul,div,rem}`, `wp_IScalar_neg`, `wp_UScalar_{shl,shr}`;
  - bit-vector conditions for `bv_decide`: `wp_UScalar_{add,sub,mul}_bvc`.
- Relational: `sim_of_wp`, `equiv_of_wp`, `equiv_of_sim_of_safe`, `equiv_of_wp_eq`, `sim_pureVal_iff`, `equiv_pureVal_iff`, and `equiv_eq_iff` (`Equiv (· = ·) t s ↔ t = s`).
**Loops.lean (2.0 s).** `loop_shape : LoopShape (loop body) body loopCls`. `loop_terminates : LoopShape.Terminates (loop body) body loopCls`, proved by fixpoint induction (`loop.fixpoint_induct`) with Aeneas' `dspec_func_admissible`. Also `equiv_loop` (lockstep, no variant) and `sim_loop'`.
**Corr.lean (1.9 s).** `Corr` instances: UScalar to Nat/BitVec, IScalar to Int/BitVec, Slice/Vec/Array to List, outcomes via `outcomeRel`. Value lemmas: `val_*_of_le`, `val_saturating_add`, `hcast_val_of_numBits_lt`.
**Tactic.lean (2.6 s)**
- `aeneas_wp [..] at loc`: symbolic execution, plus normalisation to `.val` arithmetic.
- `aeneas_leaves`: `split_ifs`, `simp_all`, then `scalar_tac`, `scalar_tac +nonLin`, `ring1`.
- `equiv_aeneas [defs] using I with [..]`: lockstep loops. It runs the source first and keeps the target abstract until the source branches are split.
- `equiv_aeneas_straight`: loop-free functions. `wp_aeneas_loop [defs] using Inv, V`: one-sided loop proofs. `equiv_aeneas_pure`: a Rust function against `pureVal`.
**Real Charon + Aeneas fdebf20 output** (`examples/rust/<crate>`, regenerate with `examples/rust/regen.sh`): Gen/Aeneas/{AcctInt, SumPR, Bits, FindPR, VecPR, MidPR}. Aeneas leaves the external `core.num.I128.abs` as an axiom; `AcctInt/FunsExternal.lean` replaces it with a hand-written definition (checked negation).
**Demos** (Demo/Aeneas):
- SumPR (4 s):
  - `v2_equiv_v1`: `Equiv (· = ·)`, so the same results and the same panics. One tactic call.
  - `v6_equiv_v5`: a caller of the changed callee, via `equiv_eq_iff`.
  - `v3_equivOn_v1`: `EquivOn Bad` for the saturating PR, with `v1_panics_iff`: Bad is exactly the set of inputs where the old version panics.
- SumUnroll (19.5 s): `v4_equiv_v1`, a loop unrolled by 2, through core `sim_loop_stutter`.
- FindPR (`find_v2_equiv_v1`, early return) and VecPR (`squares_v2_equiv_v1`, Vec push plus strength reduction): one tactic call each.
- MidPR: `v2_equivOn_v1`, `v1_panics_iff`, `v2_equiv_average`.
- AcctIntSpec (12.9 s): `accrue_spec` and `accrue_equiv_model`. Rust `accrue` equals `accrueModel` (on `Int`) on the COBOL field ranges, and never panics there.
- Popcount: `popcount_equiv_swar` (Kernighan's loop against SWAR). Fnv: `fnv1a32_equiv_fnv` (the loop against a `foldl`).
**C++ → Rust collections migration (`Demo/XLang/VecSum.lean`).** `examples/xlang/vec.cpp` is translated by cir2lean into `Gen.XVec` (`Demo/Gen/Cir/XVec.lean`); `examples/rust/xvec` is translated into `Gen/Aeneas/XVec`.
- `vsum_rust_sim_cpp`: Rust `Vec` loop ⊑ C++ `std::vector` loop. The C++ side runs in a hypothesis (`cir_hrun`); the two loops are paired by `wp_loop_rel` (Aeneas `loop_shape` against `Cir.loopShape_for`/`terminates_for`) with coupling `VsI`.
- `vsum_cpp_safe` and `vsum_equiv`: equivalence off `Bad` (a prefix sum overflows `int`, or 2^63 or more elements). Check time 14 s, std axioms.
**Axioms.** I checked 344 declarations (bridge, demos, generated code, VecSum). All use only [propext, Classical.choice, Quot.sound], except four theorems in Popcount.lean, where `bv_decide` adds `<thm>._native.bv_decide.ax_N`: swar_le, swar_step, and_sub_lt, popcount_swar_spec.
**Messages.** eq-cobol: AcctInt names, the bridge API, `accrue_spec`. An agent: Bits names, popcount and fnv specs. main: progress and the module list. **Dependents, keep names stable:** eq-cobol (Demo/Cobol/{AcctIntAeneas,RecSumAeneas}: `wp_*`, `loop_shape`, `loop_terminates`, `loopCls_*`, `IScalar.val_sdiv`/`tdiv_bounds`); an agent (Demo/TS/{FnvXLang,FnvSpec}: `bits.fnv1a32`, `loop_shape`, `loop_terminates`, `aeneas_wp`, `Fnv.fnv1a32_equiv_fnv`). **Gaps:**
- Aeneas returns 0 for signed `MIN % -1`, where Rust panics.
- `equiv_aeneas` only covers lockstep pairs with one loop per function.
- `SumUnroll.step_both` needs `maxHeartbeats 1000000`.
- Inlining large callees overflows simp; the workaround is call specifications such as `wp_div_half_up`.
- Not covered: signed shifts, the value form of signed `%`, `Vec.index_mut`.

**AutoCouple.lean (2026-10-24, helper; 4.2 s).** `equiv_aeneas [defs] (with [..])?` without `using` generates the coupling of the two loops; `equiv_aeneas … using I` is unchanged, and `equiv_aeneas?` suggests the `using` form. After unfolding `defs`, the loop variables (components of the two loop states) are paired by Rust name and type (the params of the `@[rust_loop]` defs that form the initial states), then by type and position; this gives `p = q` when all pair in order. An unpaired variable keeps its entry value when every `cont` passes it on unchanged or resets it, otherwise it is unconstrained. Loop bounds `i.val ≤ v.val.length` (`Slice.len`/`Vec.len`) or `i.val ≤ n.val` are added for a scalar `i` that the body compares (`<`, `>`, `!=`, `==`, `=`, `≠`) with a loop-invariant value. It tries the coupling without, then with the bounds. Each attempt is the `using` pipeline (`aeneas_lockstep`) without error recovery, and counts only if it closes the goal with no sorry and no new error; otherwise the goal is restored and the error lists the couplings tried (failed attempts count against `maxHeartbeats`).
- `Demo/Aeneas/AutoCouple.lean` (18.5 s): SumPR and FindPR with no coupling, both directions (the generated couplings are the hand-written ones), and three PRs of `examples/rust/autopr` (`Gen/Aeneas/AutoPR`): `sum` with its loop variables reordered and `!=`, `contains` with flag + break (the same loop after Aeneas), and `max` with a temporary declared before the loop (an extra loop variable, left unconstrained).
- `Test/AeneasAutoCouple.lean` (18.8 s): hand-written Aeneas-shaped loops for entry values and for type+position pairing, plus the VecPR fallback.
- Not generated: relations between variables (VecPR `sq = i*i`), functional invariants (SumPR v3), bounds between two loop variables, non-lockstep loops (SumUnroll), more than one loop per function. All 14 theorems use only the standard axioms.

**SpecAuto.lean (2026-10-24, helper; 5.5 s), Headline A.** `aeneas_spec [defs] (with [lemmas])?` proves `f inputs = .ok (spec inputs)` for Rust loops over a slice or `Vec` (index a `usize` compared with the length) against a Lean spec built from `List.map`/`filter`/`foldl`/`find?`/`any`: it generates the loop invariant (`i ≤ len`; each other loop variable = the spec on the prefix `take i xs`, append prefixes, decoders; search loops `(take i xs).find? p = none`), filtered by type and entry value; at most 8 atomic attempts.
- `Demo/Aeneas/SpecAuto.lean` (43.9 s, `examples/rust/speckit`, `Gen/Aeneas/SpecKit`): 18 theorems: map, header+trailer, filter, two outputs, a count with a decoder, `foldl` running totals (scalar and struct states), linear search, a loop calling it, two loops in sequence, an rc flag via `List.any`; CBACT04C's `read_account` and `find_rate` (as `List.find?`); a CBACT02C-shaped `run` (`Vec<Vec<u8>>`: start line, one line per record, end line) with `zero_pad` against `EquivLean.Cobol.Rec.zpad`.
- Not generated: counter loops `while k < n` with `n` a parameter, decreasing indices, arithmetic invariants (`zero_pad` is proved by hand), flag-driven read loops, control-break loops.
