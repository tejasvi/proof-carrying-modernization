import EquivLean.Modernize.Cbstm03a.Java.Dz.Lem

/-!
# CBSTM03A → Java `decodeZoned`: the paths from cut point 7

From `dzChar` (the character `c` at `i` read): a digit (8 … 13) or a character that is not the last one
(14, 15, 54 … 56) reaches the join `dzJoin` (57); the last character, not a digit, reaches `dzLast` (16).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows argText)

namespace EquivLean.Modernize.Cbstm03a.Java.Dz

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem dz_c7 : DzCutVC 7 dzChar := by
  unfold DzCutVC dzWP
  jvc [decodeZonedSpec, decodeZonedInv, dzChar, dzLast, dzJoin, StrNN, argText, strOf, toInt_ofNat32z,
    toInt_setWidth32, toInt_ofNat_sub_one, sw32_eq, last_iff]
  all_goals (dz_lits; first
    | exact lowd_lt _
    | exact dig_v _ _ _ ‹_› ‹_› ‹_›
    | exact mid_v _ _ _ ‹_› (by omega) (by omega)
    | exact sign_true (dig_s _ _ _ ‹_› ‹_› ‹_›) ‹_›
    | exact sign_false (dig_s _ _ _ ‹_› ‹_› ‹_›) ‹_›
    | exact sign_true (mid_s _ _ _ ‹_› (by omega) (by omega)) ‹_›
    | exact sign_false (mid_s _ _ _ ‹_› (by omega) (by omega)) ‹_›)

end EquivLean.Modernize.Cbstm03a.Java.Dz

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.dz_c7
