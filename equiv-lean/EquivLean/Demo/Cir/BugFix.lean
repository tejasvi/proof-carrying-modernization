import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.COld
import EquivLean.Demo.Gen.Cir.CNew

/-!
# Demo (c): a bug fix, stated with `EquivOn`

`examples/cir/c_old.cpp` → `c_new.cpp` (translated by clang -fclangir and cir2lean into
`EquivLean.Demo.Gen.Cir.COld` / `CNew`):

```cpp
// old: `a + b` is a signed overflow (undefined behaviour) for large inputs
int average(int a, int b) { return (a + b) / 2; }
// new: the sum is computed in 64 bits
int average(int a, int b) { return (int)(((long long)a + b) / 2); }
```

`average_equivOn`: the two versions are equivalent (same safety, same result, same
caller-visible memory) on every call outside `Bad`, the calls on which the old version
overflows (and ill-typed calls).  `average_old_ub` shows that the old version really has
undefined behaviour on every well-typed call in `Bad`, and `average_new_spec` that the new
version is safe on all of them: the patch changed behaviour exactly where the old code was
wrong.
-/

namespace EquivLean.Demo.Cir.BugFix

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

/-- The calls the fix may change: `a + b` overflows `int` (or the call is ill-typed). -/
def Bad (args : List Val) (_ : Mem) : Prop :=
  ¬ ∃ a b : Int, args = [.int a, .int b] ∧ -2147483648 ≤ a + b ∧ a + b ≤ 2147483647

theorem average_equivOn :
    Cir.EquivOn Bad CNew.ctx CNew.fn_average.sym COld.ctx COld.fn_average.sym := by
  equiv_cir

/-- On well-typed calls in `Bad` the old version has undefined behaviour. -/
theorem average_old_ub (a b : Int) (m : Mem)
    (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) (hb : -2147483648 ≤ b ∧ b ≤ 2147483647)
    (hov : a + b < -2147483648 ∨ 2147483647 < a + b) :
    ¬ Safe (evalCall COld.ctx COld.fn_average.sym [.int a, .int b] m) := by
  rw [safe_res_iff_holds]
  intro hs
  cir_hrun hs
  all_goals omega

theorem tdiv_two_bounds (s : Int) (h1 : -4294967296 ≤ s) (h2 : s ≤ 4294967295) :
    -2147483648 ≤ s.tdiv 2 ∧ s.tdiv 2 ≤ 2147483647 := by
  by_cases h : 0 ≤ s
  · rw [Int.tdiv_eq_ediv_of_nonneg h]; omega
  · have e : s = -(-s) := by omega
    rw [e, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega

/-- The new version is safe on every well-typed call and returns the truncated average. -/
theorem average_new_spec (a b : Int) (m : Mem)
    (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) (hb : -2147483648 ≤ b ∧ b ≤ 2147483647) :
    Returns CNew.ctx CNew.fn_average.sym [.int a, .int b] m
      (fun v _ => v = some (.int ((a + b).tdiv 2))) := by
  have := tdiv_two_bounds (a + b) (by omega) (by omega)
  cir_start
  cir_vcg

end EquivLean.Demo.Cir.BugFix
