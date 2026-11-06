import CIR
import Examples.GenM.Calls.F.fn_quad

/-! `quad` alone: this file imports only the module of `quad`; the contract of
its callee `twice` is a hypothesis, so a change to `twice`'s body does not
touch this proof. -/

open CIR Examples.GenM.Calls

set_option maxHeartbeats 4000000

namespace Examples.Modular

set_option cir.inline false in
/-- `int quad(int x) { return twice(twice(x)); }` from the contract of `twice`. -/
theorem quad_spec (ctx : Ctx) (hf : ctx.mod.findFunc? "_Z4quadi" = some fn_quad)
    (htwice : ∀ (x : Int) (m : Mem), -1073741824 ≤ x → x ≤ 1073741823 →
      Returns ctx "_Z5twicei" [.int x] m (fun v m' => v = some (.int (2 * x)) ∧ Frame m m' []))
    (x : Int) (m : Mem) (h1 : -536870912 ≤ x) (h2 : x ≤ 536870911) :
    Returns ctx "_Z4quadi" [.int x] m (fun v _ => v = some (.int (4 * x))) := by
  cir_start
  cir_vcg

end Examples.Modular
