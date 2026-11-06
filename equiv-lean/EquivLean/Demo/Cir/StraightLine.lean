import EquivLean.Bridge.Cir.Tactic
import EquivLean.Demo.Gen.Cir.AOld
import EquivLean.Demo.Gen.Cir.ANew

/-!
# Demo (a): a straight-line C++ refactoring

`examples/cir/a_old.cpp` → `a_new.cpp` (both translated by clang -fclangir and cir2lean into
`EquivLean.Demo.Gen.Cir.AOld` / `ANew`):

```cpp
// old                                     // new
int clamp(int x, int lo, int hi) {         int clamp(int x, int lo, int hi) {
  if (x < lo) return lo;                     return x < lo ? lo : std::min(x, hi);
  if (x > hi) return hi;                   }
  return x;
}
int max3(int a, int b, int c) {            int max3(int a, int b, int c) {
  int m = a;                                 return std::max(a, std::max(b, c));
  if (b > m) m = b;                        }
  if (c > m) m = c;
  return m;
}
```

The new versions call libc++'s `std::min`/`std::max` (cirlean's library models; they take
and return references, so the new code allocates temporaries the old one does not).  The
theorems are unconditional: for every argument value and every initial memory, both
versions are safe on the same calls and return the same value with the same caller-visible
memory (`ObsEq`).
-/

namespace EquivLean.Demo.Cir.StraightLine

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

theorem clamp_equiv (x lo hi : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall ANew.ctx ANew.fn_clamp.sym [.int x, .int lo, .int hi] m)
      (evalCall AOld.ctx AOld.fn_clamp.sym [.int x, .int lo, .int hi] m) := by
  equiv_cir

theorem max3_equiv (a b c : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall ANew.ctx ANew.fn_max3.sym [.int a, .int b, .int c] m)
      (evalCall AOld.ctx AOld.fn_max3.sym [.int a, .int b, .int c] m) := by
  equiv_cir

/-- The whole-function statement: the two versions differ at most on ill-typed calls (an
argument list that is not three `int`s, which C++ callers cannot produce). -/
theorem clamp_equivOn :
    Cir.EquivOn (fun args _ => ¬ ∃ x lo hi : Int, args = [.int x, .int lo, .int hi])
      ANew.ctx ANew.fn_clamp.sym AOld.ctx AOld.fn_clamp.sym := by
  intro args m hbad
  obtain ⟨x, lo, hi, rfl⟩ := Classical.not_not.mp hbad
  exact clamp_equiv x lo hi m

theorem max3_equivOn :
    Cir.EquivOn (fun args _ => ¬ ∃ a b c : Int, args = [.int a, .int b, .int c])
      ANew.ctx ANew.fn_max3.sym AOld.ctx AOld.fn_max3.sym := by
  intro args m hbad
  obtain ⟨a, b, c, rfl⟩ := Classical.not_not.mp hbad
  exact max3_equiv a b c m

end EquivLean.Demo.Cir.StraightLine
