import EquivLean.Demo.Thrift.Java.Cp

/-!
# Thrift → Java (T4): arithmetic and list facts of the varint loops
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The continuation byte `(byte) ((n & 0x7F) | 0x80)`. -/
theorem byteOf_cont (x : I32) :
    byteOf (.int (JInt.toByte (JInt.toByte (x &&& 127#32 ||| 128#32)))) =
      UInt8.ofNat (x.toNat % 128 + 128) := by
  rw [toByte_toByte, byteOf_toByte, cont_toNat]

theorem ofNat_succ32 (i : Nat) : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (b : α) (h : i < l.length) :
    (l.set i b).take (i + 1) = l.take i ++ [b] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_set, List.length_append, List.length_cons,
      List.length_nil]
    omega
  · intro j h1 h2
    simp only [List.length_take, List.length_set] at h1
    rw [List.getElem_take, List.getElem_set]
    by_cases hj : j < i
    · rw [if_neg (by omega), List.getElem_append_left (by simp; omega), List.getElem_take]
    · have : j = i := by omega
      subst this
      rw [if_pos rfl, List.getElem_append_right (by simp; omega)]
      simp

end EquivLean.Demo.Thrift.Java
