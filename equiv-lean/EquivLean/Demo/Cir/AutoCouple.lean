import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Demo.Gen.Cir.AOld
import EquivLean.Demo.Gen.Cir.ANew
import EquivLean.Demo.Gen.Cir.BOld
import EquivLean.Demo.Gen.Cir.BNew
import EquivLean.Demo.Gen.Cir.COld
import EquivLean.Demo.Gen.Cir.CNew
import EquivLean.Demo.Gen.Cir.CbOld
import EquivLean.Demo.Gen.Cir.CbNew

/-!
# Demo: loop pairs coupled automatically (`equiv_cir` without `using`)

With `EquivLean.Bridge.Cir.AutoCouple` imported, `equiv_cir` generates the coupling invariant of
two loops of the same shape itself (equal corresponding variables, entry values of the others,
loop bounds), so these proofs give no invariant:

* `sum_below_equiv_auto`: the `for` / `while` refactoring of `LoopRefactor` (`s = s' ∧ i = i'`);
* `count_bits_sim_auto`: `examples/cir/cb_old.cpp` → `cb_new.cpp`, the same bit-count loop
  with an extra guarded branch (`if (A == 0) break;`) inside `while (A != 0)` (`A = A' ∧
  count = count'`, `A` unsigned);
* straight-line goals are unchanged (`clamp_equiv_auto`, `average_equivOn_auto`).
-/

namespace EquivLean.Demo.Cir.AutoCouple

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 8000000

theorem sum_below_equiv_auto (n : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall BNew.ctx BNew.fn_sum_below.sym [.int n] m)
      (evalCall BOld.ctx BOld.fn_sum_below.sym [.int n] m) := by
  equiv_cir

theorem count_bits_sim_auto (a : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall CbNew.ctx CbNew.fn_count_bits.sym [.int a] m)
      (evalCall CbOld.ctx CbOld.fn_count_bits.sym [.int a] m) := by
  equiv_cir

theorem clamp_equiv_auto (x lo hi : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall ANew.ctx ANew.fn_clamp.sym [.int x, .int lo, .int hi] m)
      (evalCall AOld.ctx AOld.fn_clamp.sym [.int x, .int lo, .int hi] m) := by
  equiv_cir

/-- The calls `average` may change: `a + b` overflows (or the call is ill-typed). -/
def Bad (args : List Val) (_ : Mem) : Prop :=
  ¬ ∃ a b : Int, args = [.int a, .int b] ∧ -2147483648 ≤ a + b ∧ a + b ≤ 2147483647

theorem average_equivOn_auto :
    Cir.EquivOn Bad CNew.ctx CNew.fn_average.sym COld.ctx COld.fn_average.sym := by
  equiv_cir

end EquivLean.Demo.Cir.AutoCouple
