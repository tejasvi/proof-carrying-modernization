import EquivLean.Modernize.Cbstm03a.Java.Num.NumLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows zpadStr)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zu_vc : MethodVC Gen.prog zuCallees.env 0 zuRef zuSpec [] 40 := by
  jverify [zuSpec, zuCallees, pow10Sig, pow10Spec, zeroPadSig, zeroPadSpec, Grows]
  all_goals first
    | exact absurd ‹(10#64 : BitVec 64) ^ _ = 0#64› (pow10_ne_zero _ (by omega))
    | (rw [neg_toInt _ (by omega)]; exact Int.tmod_nonneg _ (by omega))
    | exact Int.tmod_nonneg _ (by omega)
    | (rw [zpad_srem _ (by rw [neg_toInt _ (by omega)]; omega) _ (by omega), natAbs_eq_neg_toNat _ (by omega) (by omega)])
    | (rw [zpad_srem _ (by omega) _ (by omega), natAbs_eq_toNat _ (by omega)])

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.zu_vc
