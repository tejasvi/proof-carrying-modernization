import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Demo.Gen.Cir.BdOld
import EquivLean.Demo.Gen.Cir.BdNew

/-!
# Demo: a generated coupling with a loop bound

`examples/cir/bd_old.cpp` → `bd_new.cpp`: the loop test `i < n` becomes `i != n`.  The two loops
agree only below the bound, so equality of the counters and sums is not inductive on its own;
the third attempt of the generated coupling adds `i ≤ n` (the counter is compared with `n`,
which the loop does not modify).  For `0 ≤ n` the two versions are equivalent; plain
`equiv_cir`, no coupling written.
-/

namespace EquivLean.Demo.Cir.AutoBound

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 8000000

theorem twice_equiv_auto (n : Int) (m : Mem) (hn : 0 ≤ n) :
    Equiv (ObsEq m) (evalCall BdNew.ctx BdNew.fn_twice.sym [.int n] m)
      (evalCall BdOld.ctx BdOld.fn_twice.sym [.int n] m) := by
  equiv_cir

end EquivLean.Demo.Cir.AutoBound
