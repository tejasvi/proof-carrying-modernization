import EquivLean.Bridge.Aeneas.AutoCouple
import EquivLean.Demo.Gen.Aeneas.SumPR.Funs
import EquivLean.Demo.Gen.Aeneas.FindPR.Funs
import EquivLean.Demo.Gen.Aeneas.AutoPR.Funs

/-!
# Rust loop refactorings with a generated coupling (no invariant written)

`equiv_aeneas [defs]` without `using` (`Bridge/Aeneas/AutoCouple.lean`) generates the coupling
invariant of the two loops.  All code is unmodified Charon + Aeneas output.

* The refactorings of `Demo/Aeneas/SumPR.lean` (`i != len` instead of `i < len`, zero entries
  skipped) and `Demo/Aeneas/FindPR.lean` (early `return`), whose couplings are written by hand
  there, in both directions.  The generated couplings are the hand-written ones:
  `p = q ∧ p.2.val ≤ v.val.length` and `p = q ∧ p.val ≤ v.val.length`.
* Three pull requests of `examples/rust/autopr` (`Demo/Gen/Aeneas/AutoPR/Funs.lean`) that change
  the loop variables of the translation:
  - `sum`: the index declared before the accumulator, `+=`, and `i != v.len()` as the loop
    condition.  The loop states are `(i, s)` against `(s, i)`; the variables are paired by name,
    and the bound comes from `i != v.len()`: `p.1 = q.2 ∧ p.2 = q.1 ∧ p.1.val ≤ v.val.length`;
  - `contains`: a flag and `break` instead of the early `return`.  Aeneas moves `found = true` to
    the exit of the loop, so both loops have the state `i` and the coupling is `p = q`;
  - `max`: the element variable declared in the loop instead of before it.  The original loop
    carries it as a loop variable, state `(x, m, i)` against `(m, i)`; every iteration overwrites
    it, so it is left unconstrained: `p.1 = q.2.1 ∧ p.2 = q.2.2`.

The couplings quoted are the ones `equiv_aeneas?` reports.  `Demo/Aeneas/VecPR.lean` (strength
reduction: `sq = i * i`) and `v3_equivOn_v1` of `Demo/Aeneas/SumPR.lean` (a functional invariant)
keep their hand-written couplings: no generated candidate closes them.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.AutoCouple

/-! ## `SumPR` and `FindPR` without a coupling -/

theorem sumpr_v2_equiv_v1 (v : Slice U32) :
    Equiv (· = ·) (sumpr.v2.sum v) (sumpr.v1.sum v) := by
  equiv_aeneas [sumpr.v2.sum, sumpr.v1.sum, sumpr.v2.sum_loop, sumpr.v1.sum_loop,
    sumpr.v2.sum_loop.body, sumpr.v1.sum_loop.body]

theorem sumpr_v1_equiv_v2 (v : Slice U32) :
    Equiv (· = ·) (sumpr.v1.sum v) (sumpr.v2.sum v) := by
  equiv_aeneas [sumpr.v2.sum, sumpr.v1.sum, sumpr.v2.sum_loop, sumpr.v1.sum_loop,
    sumpr.v2.sum_loop.body, sumpr.v1.sum_loop.body]

/-- Simulation only (`sim_loop'`). -/
theorem sumpr_v2_sim_v1 (v : Slice U32) :
    Sim (· = ·) (sumpr.v2.sum v) (sumpr.v1.sum v) := by
  equiv_aeneas [sumpr.v2.sum, sumpr.v1.sum, sumpr.v2.sum_loop, sumpr.v1.sum_loop,
    sumpr.v2.sum_loop.body, sumpr.v1.sum_loop.body]

theorem findpr_v2_equiv_v1 (v : Slice U32) (x : U32) :
    Equiv (· = ·) (findpr.v2.find v x) (findpr.v1.find v x) := by
  equiv_aeneas [findpr.v2.find, findpr.v1.find, findpr.v2.find_loop, findpr.v1.find_loop,
    findpr.v2.find_loop.body, findpr.v1.find_loop.body]

theorem findpr_v1_equiv_v2 (v : Slice U32) (x : U32) :
    Equiv (· = ·) (findpr.v1.find v x) (findpr.v2.find v x) := by
  equiv_aeneas [findpr.v2.find, findpr.v1.find, findpr.v2.find_loop, findpr.v1.find_loop,
    findpr.v2.find_loop.body, findpr.v1.find_loop.body]

/-! ## Pull requests that change the loop variables (`examples/rust/autopr`) -/

/-- Loop states `(i, s)` and `(s, i)`, `i != v.len()` against `i < v.len()`. -/
theorem sum_v2_equiv_v1 (v : Slice U32) : Equiv (· = ·) (autopr.v2.sum v) (autopr.v1.sum v) := by
  equiv_aeneas [autopr.v2.sum, autopr.v1.sum, autopr.v2.sum_loop, autopr.v1.sum_loop,
    autopr.v2.sum_loop.body, autopr.v1.sum_loop.body]

theorem sum_v1_equiv_v2 (v : Slice U32) : Equiv (· = ·) (autopr.v1.sum v) (autopr.v2.sum v) := by
  equiv_aeneas [autopr.v2.sum, autopr.v1.sum, autopr.v2.sum_loop, autopr.v1.sum_loop,
    autopr.v2.sum_loop.body, autopr.v1.sum_loop.body]

/-- Early `return` against flag and `break`: the same loop state after Aeneas. -/
theorem contains_v2_equiv_v1 (v : Slice U32) (x : U32) :
    Equiv (· = ·) (autopr.v2.contains v x) (autopr.v1.contains v x) := by
  equiv_aeneas [autopr.v2.contains, autopr.v1.contains, autopr.v2.contains_loop,
    autopr.v1.contains_loop, autopr.v2.contains_loop.body, autopr.v1.contains_loop.body]

/-- Loop states `(m, i)` and `(x, m, i)`: the extra variable `x` is left unconstrained. -/
theorem max_v2_equiv_v1 (v : Slice U32) : Equiv (· = ·) (autopr.v2.max v) (autopr.v1.max v) := by
  equiv_aeneas [autopr.v2.max, autopr.v1.max, autopr.v2.max_loop, autopr.v1.max_loop,
    autopr.v2.max_loop.body, autopr.v1.max_loop.body]

theorem max_v1_equiv_v2 (v : Slice U32) : Equiv (· = ·) (autopr.v1.max v) (autopr.v2.max v) := by
  equiv_aeneas [autopr.v2.max, autopr.v1.max, autopr.v2.max_loop, autopr.v1.max_loop,
    autopr.v2.max_loop.body, autopr.v1.max_loop.body]

end EquivLean.Demo.Aeneas.AutoCouple

#print axioms EquivLean.Demo.Aeneas.AutoCouple.sumpr_v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.sumpr_v1_equiv_v2
#print axioms EquivLean.Demo.Aeneas.AutoCouple.sumpr_v2_sim_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.findpr_v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.findpr_v1_equiv_v2
#print axioms EquivLean.Demo.Aeneas.AutoCouple.sum_v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.sum_v1_equiv_v2
#print axioms EquivLean.Demo.Aeneas.AutoCouple.contains_v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.max_v2_equiv_v1
#print axioms EquivLean.Demo.Aeneas.AutoCouple.max_v1_equiv_v2
