import EquivLean.Modernize.Cbstm03a.Java.Num.FmtZLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows zpadStr digitChar zpadStr_length space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- At the loop head (statement 15): `ip` holds the 9 integer digits, the first `k` of them zeros; `a` is
`|v| % 10^11`, `$z2` the sign. Locals: `a` 1, `k` 5, `ip` 7, `$z2` 12. -/
def fmtZInv : Invariants := [(15, fun args σ0 fr σ => ∀ v : I64, args = [.long v] →
  ∃ (ipa : Addr) (k : I32) (a : I64), fr.get 1 = some (.long a) ∧ fr.get 5 = some (.int k) ∧
    fr.get 7 = some (.ref ipa) ∧ fr.get 12 = some (.int (if v.toInt < 0 then 1#32 else 0#32)) ∧
    0 ≤ a.toInt ∧ a.toNat = v.toInt.natAbs % 100000000000 ∧
    σ.heap ipa = some (.str (zpadStr (v.toInt.natAbs / 100) 9)) ∧
    0 ≤ k.toInt ∧ k.toInt ≤ 9 ∧ k.toInt.toNat ≤ lead0 (zpadStr (v.toInt.natAbs / 100) 9) ∧
    σ0.next ≤ ipa ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbstm03a" = .done)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
set_option jimple.modelContracts true in
theorem fmtZ_vc : MethodVC Gen.prog fmtCallees.env 0 fmtZRef fmtZSpec fmtZInv 60 := by
  jverify [fmtZSpec, fmtZInv, fmtCallees, zeroPadSig, zeroPadSpec, spacesSig, spacesSpecI, Grows, zpadStr_length]
  all_goals first
    | with_reducible exact srem11_toNat_neg _ ‹_› ‹_›
    | with_reducible exact srem11_toNat_pos _ ‹_›
    | with_reducible exact ip_neg _ ‹_› ‹_›
    | with_reducible exact ip_pos _ ‹_›
    | (exfalso; simp only [List.getElem?_eq_none_iff, zpadStr_length] at *; omega)
    | with_reducible_and_instances exact lead0_step' _ _ _ (by omega) ‹_› ‹_› ‹_›
    | (apply fmtZ_nine_pos <;> assumption)
    | (apply fmtZ_nine_neg <;> assumption)
    | (apply fmtZ_stop_pos <;> assumption)
    | (apply fmtZ_stop_neg <;> assumption)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtZ_vc
