import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.EOld
import EquivLean.Demo.Gen.Cir.ENew

/-!
# Demo (b2): a search loop, early `return` refactored into `break`

`examples/cir/e_old.cpp` → `e_new.cpp` (translated by clang -fclangir and cir2lean into
`EquivLean.Demo.Gen.Cir.EOld` / `ENew`):

```cpp
// old                                     // new
int find_first(int n, int k) {             int find_first(int n, int k) {
  for (int i = 0; i < n; ++i)                int r = -1;
    if (i * i >= k) return i;                for (int i = 0; i < n; ++i) {
  return -1;                                   if (i * i >= k) { r = i; break; }
}                                            }
                                             return r;
                                           }
```

The loops leave in different ways on a hit: the old one with `Step.exit (.ret i)` (a
`return` through the loop), the new one with `Step.next` (`break`), after which it loads and
returns `r`.  `cir_loop_pair` relates the loop outcomes by "the continuations agree", so the
code after the loops is executed inside the iteration that leaves them and no relation
between the two exit kinds has to be written.  Coupling invariant: `r = -1` (the new
version's result variable stays `-1` while the loops run) and equal counters.  Both versions
overflow on `i * i` at the same iteration, so the statement is unconditional.
-/

namespace EquivLean.Demo.Cir.EarlyExit

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

/-- new ⊑ old (binders: `r i` the new version's variables, `i'` the old one's). -/
theorem find_first_sim (n k : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall ENew.ctx ENew.fn_find_first.sym [.int n, .int k] m)
      (evalCall EOld.ctx EOld.fn_find_first.sym [.int n, .int k] m) := by
  cir_sim_loop (fun r i i' => r = -1 ∧ i = i')

/-- old ⊑ new (binders: `i` the old version's variable, `r' i'` the new one's). -/
theorem find_first_sim_rev (n k : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall EOld.ctx EOld.fn_find_first.sym [.int n, .int k] m)
      (evalCall ENew.ctx ENew.fn_find_first.sym [.int n, .int k] m) := by
  cir_sim_loop (fun i r' i' => r' = -1 ∧ i = i')

theorem find_first_equivOn :
    Cir.EquivOn (fun args _ => ¬ ∃ n k : Int, args = [.int n, .int k])
      ENew.ctx ENew.fn_find_first.sym EOld.ctx EOld.fn_find_first.sym := by
  refine EquivOn.intro (fun args m hbad => ?_) (fun args m hbad => ?_) <;>
    obtain ⟨n, k, rfl⟩ := Classical.not_not.mp hbad
  · exact find_first_sim n k m
  · exact find_first_sim_rev n k m

end EquivLean.Demo.Cir.EarlyExit
