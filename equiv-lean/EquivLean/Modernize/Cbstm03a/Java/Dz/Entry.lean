import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem

/-!
# CBSTM03A → Java `decodeZoned`: the entry path

Statements 0 … 4 (`v = 0`, `neg = false`, `n = s.length()`, `i = 0`) reach the loop head `dzHead` (5).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem dz_entry : DzEntryVC := by
  unfold DzEntryVC dzWP
  jvc [decodeZonedSpec, decodeZonedInv, dzHead, StrNN, argText, strOf, toInt_ofNat32z,
    toInt_setWidth32]

end EquivLean.Modernize.Cbstm03a.Java.Dz

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.dz_entry
