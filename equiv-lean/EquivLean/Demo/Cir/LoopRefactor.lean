import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.BOld
import EquivLean.Demo.Gen.Cir.BNew

/-!
# Demo (b): a loop refactoring, proved with lockstep loops

`examples/cir/b_old.cpp` → `b_new.cpp` (translated by clang -fclangir and cir2lean into
`EquivLean.Demo.Gen.Cir.BOld` / `BNew`):

```cpp
// old                                     // new
int sum_below(int n) {                     int sum_below(int n) {
  int s = 0;                                 int s = 0;
  for (int i = 0; i < n; ++i) s += i;        int i = 0;
  return s;                                  while (i < n) {
}                                              s = s + i;
                                               i++;
                                             }
                                             return s;
                                           }
```

A `cir.for` against a `cir.while` (different loop constructs, a scope inside the new body,
different SSA numbering).  The loops are paired in lockstep by `wp_loop_rel` with the
coupling invariant `s = s' ∧ i = i'` (`x` the target's variable, `x'` the source's); no
variant is needed, termination comes from the source loop (`terminates_for`,
`terminates_while`, proved by fixpoint induction over cirlean's interpreter).  The statement
is unconditional: in particular, both versions overflow (undefined behaviour) on exactly the
same inputs, so no precondition on `n` is needed.
-/

namespace EquivLean.Demo.Cir.LoopRefactor

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

theorem sum_below_equiv (n : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall BNew.ctx BNew.fn_sum_below.sym [.int n] m)
      (evalCall BOld.ctx BOld.fn_sum_below.sym [.int n] m) := by
  equiv_cir using (fun s i s' i' => s = s' ∧ i = i')

theorem sum_below_equivOn :
    Cir.EquivOn (fun args _ => ¬ ∃ n : Int, args = [.int n])
      BNew.ctx BNew.fn_sum_below.sym BOld.ctx BOld.fn_sum_below.sym := by
  intro args m hbad
  obtain ⟨n, rfl⟩ := Classical.not_not.mp hbad
  exact sum_below_equiv n m

end EquivLean.Demo.Cir.LoopRefactor
