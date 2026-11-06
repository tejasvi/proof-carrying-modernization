import CIR
import Examples.GenL.Linked

/-!
  Linking translation units (`cir2lean --link`, `Examples/cpp/link_a.cpp` and
  `link_b.cpp`). `run` in unit a calls `twice`, defined in unit b; each unit
  has its own `static int helper` (and its own string literal). The linked
  module keeps both helpers apart, as `link_a$_ZL6helperi` and
  `link_b$_ZL6helperi`, so a call across units is proved against the callee's
  definition in the other unit.
-/

open CIR Examples.GenL.Linked

namespace Examples.Link

/-- `run() = twice(helper_a(3)) = helper_b(4) / 5 = 8`. -/
theorem run_ok : Returns ctx "run" [] module.initMem (fun r _ => r = some (.int 8)) := by
  cir_kernel

end Examples.Link
