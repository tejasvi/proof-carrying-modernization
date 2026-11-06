import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem

/-!
# CBSTM03A → Java `decodeZoned`: the paths from cut point 57 (the join)

From `dzJoin`: `v = v * 10 + (long) d; i = i + 1` (57 … 61) returns to the loop head `dzHead` (5).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem dz_c57 : DzCutVC 57 dzJoin := by
  unfold DzCutVC dzWP
  jvc [decodeZonedSpec, decodeZonedInv, dzHead, dzJoin, StrNN, argText, strOf, toInt_ofNat32z,
    toInt_setWidth32]
  all_goals first
    | exact step64 _ _ ‹_›

end EquivLean.Modernize.Cbstm03a.Java.Dz

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.dz_c57
