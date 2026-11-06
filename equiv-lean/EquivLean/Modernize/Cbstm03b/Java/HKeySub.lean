import EquivLean.Modernize.Cbstm03b.Java.Base

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-- `keySub` for fixed ghost values: the area at `q` (fields `fs`), its key string at `skey` (25 characters) and
its key length `kl`. -/
def keySubG (q skey : Addr) (fs : List (FieldKey × Value)) (key : JStr) (kl : Int) : Spec := Spec.of
  (fun args σ => args = [.ref q] ∧ σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fs) ∧
     Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKey") = some (.ref skey) ∧ σ.heap skey = some (.str key) ∧
     key.length = 25 ∧ Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
     -10000 < kl ∧ kl < 10000)
  (fun _ σ r σ' => ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (key.take kl.toNat)) ∧ Grows σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem ofInt64_eq_zero {k : Int} (h1 : -10000 < k) (h2 : k < 10000) (h : BitVec.ofInt 64 k = 0#64) : k = 0 := by
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofInt] at e
  simp at e
  omega

theorem long_to_int_small {k : Int} (h1 : 0 ≤ k) (h2 : k < 10000) :
    BitVec.toInt (JLong.toInt (BitVec.ofInt 64 k)) = k := by
  have hn : (JLong.toInt (BitVec.ofInt 64 k)).toNat = k.toNat := by
    simp only [JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    omega
  rw [BitVec.toInt_eq_toNat_cond, hn]
  split <;> omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem keySub_vc (q skey : Addr) (fs : List (FieldKey × Value)) (key : JStr) (kl : Int) :
    MethodVC Gen.prog (fun _ => none) 0 keySubRef (keySubG q skey fs key kl) [] 60 := by
  jverify [keySubG, Grows]
  all_goals first
    | (left; have := ofInt64_eq_zero (by assumption) (by assumption) (by assumption); omega)
    | (rw [long_to_int_small (by omega) (by omega)])
    | (exfalso; rw [long_to_int_small (by omega) (by omega)] at *; omega)

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.keySub_vc
