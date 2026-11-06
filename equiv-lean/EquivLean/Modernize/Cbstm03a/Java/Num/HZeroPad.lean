import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows zpadStr digitChar sdiv10_toNat_of_nonneg sdiv10_nonneg
  srem10_of_nonneg drop_set_self)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The character `zeroPad` stores: `(char) (int) (48L + l % 10)`. -/
theorem digit_char_l (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (JLong.toInt (48#64 + l.srem 10#64))).setWidth 16 = digitChar (l.toNat % 10) := by
  rw [srem10_of_nonneg l h]
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- At the loop head (statement 5): positions `i+1 …` of the array hold the digits written so far, and the rest
of the number is `l`. Locals: `x#1` 2, `i#2` 6, `c` 7. -/
def zeroPadInv : Invariants := [(5, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 6 = some (.int i) ∧ fr.get 2 = some (.long l) ∧ fr.get 7 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ l.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadStr v.toNat n.toInt.toNat =
      zpadStr l.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zeroPad_vc : MethodVC Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpec zeroPadInv 80 := by
  jverify [ite_nat_ne, zeroPadSpec, zeroPadInv, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char_l, drop_set_self]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.zeroPad_vc
