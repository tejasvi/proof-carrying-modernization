import EquivLean.Modernize.Cbstm03a.Java.Num.ZsLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows zpadStr digitChar zpadStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- After `zeroPad` (statement 17): `z` holds the last `n` digits of `|v|`, `$z2` the sign.
Locals: `n` 4, `z` 6, `$z2` 8. -/
def zsInv : Invariants := [(17, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ za, fr.get 4 = some (.int n) ∧ fr.get 6 = some (.ref za) ∧
    fr.get 8 = some (.int (if v.toInt < 0 then 1#32 else 0#32)) ∧ 1 ≤ n.toInt ∧
    σ.heap za = some (.str (zpadStr v.toInt.natAbs n.toInt.toNat)) ∧ σ0.next ≤ za ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
set_option jimple.modelContracts true in
theorem zs_vc : MethodVC Gen.prog zuCallees.env 0 zsRef zsSpec zsInv 60 := by
  jverify [zsSpec, zsInv, zuCallees, pow10Sig, pow10Spec, zeroPadSig, zeroPadSpec, Grows, zpadStr_length,
    zpadStr_getElem?_last]
  all_goals first
    | with_reducible exact absurd ‹(10#64 : BitVec 64) ^ _ = 0#64› (pow10_ne_zero _ (by omega))
    | with_reducible (rw [neg_toInt _ (by omega)]; exact Int.tmod_nonneg _ (by omega))
    | with_reducible exact Int.tmod_nonneg _ (by omega)
    | with_reducible (rw [zpad_srem _ (by rw [neg_toInt _ (by omega)]; omega) _ (by omega), natAbs_eq_neg_toNat _ (by omega) (by omega)])
    | with_reducible (rw [zpad_srem _ (by omega) _ (by omega), natAbs_eq_toNat _ (by omega)])
    | with_reducible exact zs_close _ _ (by omega) (by omega) _ (ovp_close_pos0 _ ‹_› ‹_›)
    | with_reducible exact zs_close _ _ (by omega) (by omega) _ (ovp_close_pos _ ‹_› ‹_›)
    | with_reducible exact zs_close _ _ (by omega) (by omega) _ (ovp_close_neg0 _ ‹_› ‹_›)
    | with_reducible exact zs_close _ _ (by omega) (by omega) _ (ovp_close_neg _ ‹_› ‹_›)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.zs_vc
