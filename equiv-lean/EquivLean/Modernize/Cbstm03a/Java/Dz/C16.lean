import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem16

/-!
# CBSTM03A → Java `decodeZoned`: the paths from cut point 16 (the last character, not a digit)

From `dzLast`: the overpunch cases (17 … 53: `{`, `A`–`I`, `}`, `J`–`R`, `p`–`y`, any other character) reach the
join `dzJoin` (57) with `zLast`'s digit and sign.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

set_option maxRecDepth 8000 in
set_option maxHeartbeats 12000000 in
theorem dz_c16 : DzCutVC 16 dzLast := by
  unfold DzCutVC dzWP
  jvc [decodeZonedSpec, decodeZonedInv, dzLast, dzJoin, StrNN, argText, strOf, toInt_ofNat32z,
    toInt_setWidth32, sw32_eq]
  all_goals (dz_lits; first
    | exact lowd_lt _
    | exact last_v0 _ _ _ ‹_› ‹_› (by omega)
    | exact last_vAI _ _ _ ‹_› ‹_› (by omega)
    | exact last_vJR _ _ _ ‹_› ‹_› (by omega)
    | exact last_vpy _ _ _ ‹_› ‹_› (by omega)
    | exact last_voth _ _ _ ‹_› ‹_› ‹_› (by omega)
    | exact last_s_neg _ _ _ ‹_› ‹_› ‹_› (by omega)
    | exact sign_true (last_s_keep _ _ _ ‹_› ‹_› ‹_› (by omega)) ‹_›
    | exact sign_false (last_s_keep _ _ _ ‹_› ‹_› ‹_› (by omega)) ‹_›)

end EquivLean.Modernize.Cbstm03a.Java.Dz

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.dz_c16
