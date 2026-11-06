import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: simp helpers (3)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- `jline (Model.cps bs)` with `jline` unfolded. -/
theorem map_cps (bs : List UInt8) : List.map (BitVec.ofNat 16) (Model.cps bs) = cp037Str bs :=
  jline_cps bs

end EquivLean.Modernize.Cbtrn03c.Java.Top
