import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Demo.Gen.Cir.EOld
import EquivLean.Demo.Gen.Cir.ENew

/-!
# Demo: the early-exit refactoring with a generated coupling

The `EarlyExit` refactoring (`return` inside the loop vs a result variable and `break`, see
`Demo/Cir/EarlyExit.lean`) proved by plain `equiv_cir`, in both directions, with no coupling
written: the generated coupling pairs the loop counters and keeps the result variable `r`,
which only the new loop modifies, at its entry value `-1` (`Bridge/Cir/AutoCouple.lean`).
-/

namespace EquivLean.Demo.Cir.AutoEarlyExit

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 8000000

theorem find_first_sim_auto (n k : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall ENew.ctx ENew.fn_find_first.sym [.int n, .int k] m)
      (evalCall EOld.ctx EOld.fn_find_first.sym [.int n, .int k] m) := by
  equiv_cir

theorem find_first_sim_rev_auto (n k : Int) (m : Mem) :
    Sim (ObsEq m) (evalCall EOld.ctx EOld.fn_find_first.sym [.int n, .int k] m)
      (evalCall ENew.ctx ENew.fn_find_first.sym [.int n, .int k] m) := by
  equiv_cir

end EquivLean.Demo.Cir.AutoEarlyExit
