import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem

/-!
# CBSTM03A → Java `decodeZoned`: the paths from cut point 5 (the loop head)

From `dzHead`: `i >= n` returns `neg ? -v : v` (62 … 64), the contract's value; otherwise `c = s.charAt(i)`
(6) reaches `dzChar` (7).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem dz_c5 : DzCutVC 5 dzHead := by
  unfold DzCutVC dzWP
  jvc [decodeZonedSpec, decodeZonedInv, dzHead, dzChar, StrNN, argText, strOf, toInt_ofNat32z,
    toInt_setWidth32, zonedVal]
  all_goals first
    | exact dz_exit_neg _ _ (by omega)
    | exact dz_exit_pos _ _ (by omega)

end EquivLean.Modernize.Cbstm03a.Java.Dz

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.dz_c5
