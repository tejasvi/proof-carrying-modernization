import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

theorem ofNat_pow10_succ (k : Nat) :
    BitVec.ofNat 64 (10 ^ k) * 10#64 = BitVec.ofNat 64 (10 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.pow_succ, Nat.mod_mul_mod]

/-- At the loop head (statement 3): `p = 10 ^ i`, the state unchanged. Locals: `n` 0, `i` 1, `p` 2. -/
def pow10Inv : Invariants := [(3, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧
    fr.get 2 = some (.long (BitVec.ofNat 64 (10 ^ i.toInt.toNat))) ∧
    0 ≤ i.toInt ∧ (i.toInt ≤ n.toInt ∨ i.toInt = 0) ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem pow10_vc : MethodVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv 40 := by
  jverify [ite_nat_ne, pow10Spec, pow10Inv, ofNat_pow10_succ]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.pow10_vc
