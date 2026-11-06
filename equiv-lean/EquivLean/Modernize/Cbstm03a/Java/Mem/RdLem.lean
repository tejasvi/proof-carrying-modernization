import EquivLean.Modernize.Cbstm03a.Java.Mem.RdDefs

/-!
# CBSTM03A → Java: `memRead`, the arithmetic of a loop step

`o = off + (long) pos` without overflow on the invariant's ranges, and `within = (int) (o - slotStart(idx))`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

theorem i2l_toInt (pos : I32) : (JInt.toLong pos).toInt = pos.toInt := by
  unfold JInt.toLong
  rw [BitVec.toInt_signExtend]
  simp only [show min 64 32 = 32 from rfl]
  exact bmod32_self (by have := BitVec.le_toInt (x := pos); omega) (by have := BitVec.toInt_lt (x := pos); omega)

theorem rd_o_toInt (off : I64) (pos n : I32) (h1 : -2147483648 < off.toInt) (h2 : 0 ≤ pos.toInt)
    (h3 : pos.toInt < n.toInt) (h4 : pos.toInt = 0 ∨ off.toInt < 171156) :
    (off + JInt.toLong pos).toInt = off.toInt + pos.toInt := by
  have hol := BitVec.toInt_lt (x := off)
  have hnl := BitVec.toInt_lt (x := n)
  simp only [Nat.reduceSub] at hol hnl
  rw [BitVec.toInt_add, i2l_toInt]
  exact bmod64_self (by omega) (by rcases h4 with h | h <;> omega)

theorem rd_o_toNat (off : I64) (pos : I32) (h : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (h0 : 0 ≤ off.toInt + pos.toInt) : (off + JInt.toLong pos).toNat = (off.toInt + pos.toInt).toNat := by
  have e := toInt_eq_toNat_of_nonneg (off + JInt.toLong pos) (by omega)
  omega

theorem rd_within (o : I64) (S J : Nat) (hJ : o.toInt = J) (hS : S ≤ J) (hJS : J < 171156) :
    (JLong.toInt (o - BitVec.ofNat 64 S)).toInt = ((J - S : Nat) : Int) := by
  have hS' : (BitVec.ofNat 64 S).toInt = S := by
    rw [toInt_eq_toNat_of_lt _ (by simp only [BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  have hd : (o - BitVec.ofNat 64 S).toInt = ((J - S : Nat) : Int) := by
    rw [BitVec.toInt_sub, hJ, hS']
    rw [bmod64_self (by omega) (by omega)]
    omega
  unfold JLong.toInt
  rw [BitVec.toInt_setWidth]
  have e := toInt_eq_toNat_of_nonneg (o - BitVec.ofNat 64 S) (by omega)
  rw [show ((o - BitVec.ofNat 64 S).toNat : Int) = ((J - S : Nat) : Int) by omega]
  exact bmod32_self (by omega) (by omega)

end EquivLean.Modernize.Cbstm03a.Java.Mem
