import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.MOld
import EquivLean.Demo.Gen.Cir.MNew

/-!
# Demo (b4): two loops in sequence

`examples/cir/m_old.cpp` → `m_new.cpp` (translated by clang -fclangir and cir2lean into
`EquivLean.Demo.Gen.Cir.MOld` / `MNew`):

```cpp
// old                                      // new
int sum_then_count(int n) {                 int sum_then_count(int n) {
  int s = 0;                                  int s = 0;
  for (int i = 0; i < n; ++i) s += i;         int i = 0;
  int c = 0;                                  while (i < n) { s = s + i; i++; }
  for (int j = 0; j < s; ++j) c += 1;         int c = 0;
  return c;                                   for (int j = 0; j < s; j++) c++;
}                                             return c;
                                            }
```

`equiv_cir using [inv₁, inv₂]` (here once per direction) pairs the first loops with `inv₁`; the code after them (which
contains the second loops) runs inside the iteration that leaves the first loops, where the
second loops are paired with `inv₂`.  The second loops read `s`, fixed by the first ones.
-/

namespace EquivLean.Demo.Cir.TwoLoops

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 8000000

theorem sum_then_count_sim (n : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall MNew.ctx MNew.fn_sum_then_count.sym [.int n] m)
      (evalCall MOld.ctx MOld.fn_sum_then_count.sym [.int n] m) := by
  equiv_cir using [(fun s i s' i' => s = s' ∧ i = i'), (fun c j c' j' => c = c' ∧ j = j')]

theorem sum_then_count_sim_rev (n : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall MOld.ctx MOld.fn_sum_then_count.sym [.int n] m)
      (evalCall MNew.ctx MNew.fn_sum_then_count.sym [.int n] m) := by
  equiv_cir using [(fun s i s' i' => s = s' ∧ i = i'), (fun c j c' j' => c = c' ∧ j = j')]

theorem sum_then_count_equiv (n : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall MNew.ctx MNew.fn_sum_then_count.sym [.int n] m)
      (evalCall MOld.ctx MOld.fn_sum_then_count.sym [.int n] m) :=
  ⟨sum_then_count_sim n m, by rw [obsEq_flip]; exact sum_then_count_sim_rev n m⟩

end EquivLean.Demo.Cir.TwoLoops
