import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: the transaction and reject counters (`(c + 1) % 10^9` on `long`)
-/

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem cnt_succ (n : Nat) :
    (BitVec.ofNat 64 (n % 1000000000) + 1#64).srem 1000000000#64 =
      BitVec.ofNat 64 ((n + 1) % 1000000000) := by
  have ha : n % 1000000000 < 1000000000 := Nat.mod_lt _ (by decide)
  have h1 : BitVec.ofNat 64 (n % 1000000000) + 1#64 = BitVec.ofNat 64 (n % 1000000000 + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [h1]
  have hmsb : (BitVec.ofNat 64 (n % 1000000000 + 1)).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
    omega
  have h10 : (1000000000#64).msb = false := by decide
  rw [BitVec.srem_eq, hmsb, h10]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have h2 : n % 1000000000 + 1 < 18446744073709551616 := by omega
  have h3 : (n + 1) % 1000000000 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  omega

end EquivLean.Modernize.Cbtrn02c.Java
