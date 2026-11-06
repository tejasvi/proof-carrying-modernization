import EquivLean.Modernize.Cbstm03b.Java.Base

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

theorem msb32_false_of_nonneg (w : BitVec 32) (h : 0 ≤ w.toInt) : w.msb = false := by
  have := BitVec.toInt_eq_toNat_cond w
  have hl := w.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * w.toNat < 2 ^ 32
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem toNat_of_nonneg32 (w : BitVec 32) (h : 0 ≤ w.toInt) : (w.toNat : Int) = w.toInt := by
  have := BitVec.toInt_eq_toNat_cond w
  split at this <;> omega

theorem srem100_self (w : BitVec 32) (h0 : 0 ≤ w.toInt) (h1 : w.toInt < 100) : w.srem 100#32 = w := by
  have hm := msb32_false_of_nonneg w h0
  have hn := toNat_of_nonneg32 w h0
  have h100 : (100#32).msb = false := by decide
  rw [BitVec.srem_eq, hm, h100]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.umod_eq, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- `status2`'s first character: `(char) ('0' + v / 10)`. -/
theorem status2_hi (w : BitVec 32) (h0 : 0 ≤ w.toInt) (h1 : w.toInt < 100) :
    BitVec.setWidth 16 (JInt.toChar (48#32 + (w.srem 100#32).sdiv 10#32)) = digitChar (w.toInt.toNat / 10) := by
  have hm := msb32_false_of_nonneg w h0
  have hn := toNat_of_nonneg32 w h0
  have h10 : (10#32).msb = false := by decide
  rw [srem100_self w h0 h1, BitVec.sdiv_eq, hm, h10]
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.udiv_eq, BitVec.toNat_udiv, Nat.reducePow, Nat.reduceMod]
  omega

/-- `status2`'s second character: `(char) ('0' + v % 10)`. -/
theorem status2_lo (w : BitVec 32) (h0 : 0 ≤ w.toInt) (h1 : w.toInt < 100) :
    BitVec.setWidth 16 (JInt.toChar (48#32 + (w.srem 100#32).srem 10#32)) = digitChar (w.toInt.toNat % 10) := by
  have hm := msb32_false_of_nonneg w h0
  have hn := toNat_of_nonneg32 w h0
  have h10 : (10#32).msb = false := by decide
  rw [srem100_self w h0 h1, BitVec.srem_eq, hm, h10]
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.umod_eq, BitVec.toNat_umod, Nat.reducePow, Nat.reduceMod]
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem status2_vc : MethodVC Gen.prog (fun _ => none) 0 status2Ref status2Spec [] 40 := by
  jverify [status2Spec, stChars, Grows, status2_hi, status2_lo]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.status2_vc
