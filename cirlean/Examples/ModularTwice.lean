import CIR
import Examples.GenM.Calls.F.fn_twice

/-! `twice` alone: this file imports only the module of `twice`. -/

open CIR Examples.GenM.Calls

set_option maxHeartbeats 4000000

namespace Examples.Modular

/-- `int twice(int x) { return x + x; }` in any context that contains it. -/
theorem twice_spec (ctx : Ctx) (hf : ctx.mod.findFunc? "_Z5twicei" = some fn_twice)
    (x : Int) (m : Mem) (h1 : -1073741824 ≤ x) (h2 : x ≤ 1073741823) :
    Returns ctx "_Z5twicei" [.int x] m (fun v m' => v = some (.int (2 * x)) ∧ Frame m m' []) := by
  cir_start
  cir_vcg

end Examples.Modular
