import CIR
import Examples.GenM.Calls
import Examples.ModularTwice
import Examples.ModularQuad

/-!
  Per-function proofs (`cir2lean --modular`, `Examples/GenM/Calls/`).

  Each function of `calls.cpp` has its own module `Examples.GenM.Calls.F.fn_*`
  (`manifest.json` lists them with a hash of each definition and its callees).
  A proof states its theorem over an abstract context `ctx` that contains the
  function (`ctx.mod.findFunc? sym = some fn_f`) and takes the contracts of the
  callees as hypotheses. `Examples/ModularTwice.lean` and
  `Examples/ModularQuad.lean` import only the module of their own function:
  a change to another function does not invalidate them.

  The assembly below instantiates them with the concrete module: `cir_lookup`
  proves the lookup facts, and each callee contract is the callee's theorem.
-/

open CIR Examples.GenM.Calls

namespace Examples.Modular

/-- `quad` in the module of `calls.cpp`. -/
theorem quad_in_module (x : Int) (m : Mem) (h1 : -536870912 ≤ x) (h2 : x ≤ 536870911) :
    Returns ctx "_Z4quadi" [.int x] m (fun v _ => v = some (.int (4 * x))) :=
  quad_spec ctx (by cir_lookup) (fun y m' hy1 hy2 => twice_spec ctx (by cir_lookup) y m' hy1 hy2) x m h1 h2

end Examples.Modular
