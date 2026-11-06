import EquivLean.Modernize.Cbstm03a.Java.Num.AppLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem toInt_ofNat32' (L : Nat) (h : L < 2147483648) : (BitVec.ofNat 32 L).toInt = L := by
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 L)
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

theorem take_eq_of_min {α : Type} (l : List α) (n m : Nat) (h : min n l.length = min m l.length) :
    l.take n = l.take m := by
  apply List.ext_getElem
  · simp only [List.length_take]; exact h
  · intro i h1 h2
    simp only [List.getElem_take]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem app_vc : MethodVC Gen.prog (fun _ => none) 0 appRef appSpec [] 60 := by
  jverify [appSpec, StrNN, StrOk, argText, strOf, Keeps, toInt_ofNat32', indexOf_bmod, indexOf_emod, indexOf_le_eq]
  all_goals (
    simp only [appStr, cutAt]
    split_ifs <;> (try simp only [List.take_take]) <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; exact (List.take_of_length_le (by omega)).symm)
      | (congr 1; exact take_eq_of_min _ _ _ (by omega))
      | (congr 1; exact (List.take_of_length_le (by simp only [List.length_take] at *; omega)).symm)
      | (congr 1; exact take_eq_of_min _ _ _ (by simp only [List.length_take] at *; omega)))

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.app_vc
