import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Demo.Gen.Cir.CbOld
import EquivLean.Demo.Gen.Cir.CbNew

/-!
# Demo: a loop with an extra guarded branch, full equivalence with a generated coupling

`examples/cir/cb_old.cpp` → `cb_new.cpp`: the same bit-count loop `while (A != 0)` with an
extra `if (A == 0) break;` inside (a guard that never fires on the loop's own runs).  Plain
`equiv_cir` proves full equivalence (both simulation directions) with the generated coupling
`A = A' ∧ count = count'`; `Demo/Cir/AutoCouple.lean` has the one-direction version.
-/

namespace EquivLean.Demo.Cir.AutoCountBits

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 8000000

theorem count_bits_equiv_auto (a : Int) (m : Mem) :
    Equiv (ObsEq m) (evalCall CbNew.ctx CbNew.fn_count_bits.sym [.int a] m)
      (evalCall CbOld.ctx CbOld.fn_count_bits.sym [.int a] m) := by
  equiv_cir

end EquivLean.Demo.Cir.AutoCountBits
