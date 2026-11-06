import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-! # `ebcCompare`'s scan over the padded texts -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (fixStr fixStr_eq_map fixStr_length space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem fixStr_getElem (s : JStr) (M i : Nat) (hi : i < (fixStr s M).length) :
    (fixStr s M)[i] = s.getD i space := by
  simp only [fixStr_eq_map, List.getElem_map, List.getElem_range]

theorem fixStr_drop (s : JStr) (M i : Nat) (hi : i < M) :
    (fixStr s M).drop i = s.getD i space :: (fixStr s M).drop (i + 1) := by
  have h : i < (fixStr s M).length := by rw [fixStr_length]; exact hi
  rw [List.drop_eq_getElem_cons h, fixStr_getElem]

theorem scan_cont (sa sb : JStr) (M i : Nat) (hi : i < M)
    (h : ¬ (sa.getD i space ≠ sb.getD i space ∧ ebcIdx (sa.getD i space).toNat ≠ ebcIdx (sb.getD i space).toNat)) :
    ebcScan ((fixStr sa M).drop i) ((fixStr sb M).drop i) =
      ebcScan ((fixStr sa M).drop (i + 1)) ((fixStr sb M).drop (i + 1)) := by
  rw [fixStr_drop sa M i hi, fixStr_drop sb M i hi, ebcScan, if_neg h]

theorem scan_ret (sa sb : JStr) (M i : Nat) (hi : i < M) (h1 : sa.getD i space ≠ sb.getD i space)
    (h2 : ebcIdx (sa.getD i space).toNat ≠ ebcIdx (sb.getD i space).toNat) :
    ebcScan ((fixStr sa M).drop i) ((fixStr sb M).drop i) =
      if ebcIdx (sa.getD i space).toNat < ebcIdx (sb.getD i space).toNat then -1 else 1 := by
  rw [fixStr_drop sa M i hi, fixStr_drop sb M i hi, ebcScan, if_pos ⟨h1, h2⟩]

theorem scan_end (sa sb : JStr) (M k : Nat) (hk : M ≤ k) :
    ebcScan ((fixStr sa M).drop k) ((fixStr sb M).drop k) = 0 := by
  rw [List.drop_eq_nil_of_le (by rw [fixStr_length]; exact hk)]
  rfl

theorem ebcCmp_self (s : JStr) : ebcCmp s s = 0 := by simp [ebcCmp]

theorem ebcCmp_ne (a b : JStr) (h : ¬ b = a) :
    ebcCmp a b = ebcScan (fixStr a (max a.length b.length)) (fixStr b (max a.length b.length)) := by
  simp [ebcCmp, show ¬ a = b from fun e => h e.symm]

theorem ebcGo_le (c : Nat) : ∀ (ts : List Nat) (i : Nat), i + ts.length ≤ 256 → ebcGo c ts i ≤ 256 + c
  | [], _, _ => Nat.le_refl _
  | t :: ts, i, h => by
    simp only [ebcGo]
    split
    · simp only [List.length_cons] at h; omega
    · exact ebcGo_le c ts (i + 1) (by simp only [List.length_cons] at h; omega)

set_option maxRecDepth 20000 in
theorem ebcIdx_le (c : Nat) : ebcIdx c ≤ 256 + c := ebcGo_le c cp037Table 0 (by decide)

theorem space_setWidth : BitVec.setWidth 32 space = 32#32 := by decide

theorem setWidth32_inj (c d : JChar) : BitVec.setWidth 32 c = BitVec.setWidth 32 d ↔ c = d := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    have hc := c.isLt
    have hd := d.isLt
    simp only [BitVec.toNat_setWidth, Nat.reducePow] at this
    omega
  · rintro rfl
    rfl

theorem setWidth32_toNat (c : JChar) : (BitVec.setWidth 32 c).toNat = c.toNat := by
  have hc := c.isLt
  simp only [BitVec.toNat_setWidth, Nat.reducePow]
  omega

theorem ebc_ofNat_inj (x y : JChar) :
    BitVec.ofNat 32 (ebcIdx x.toNat) = BitVec.ofNat 32 (ebcIdx y.toNat) ↔ ebcIdx x.toNat = ebcIdx y.toNat := by
  have hx := ebcIdx_le x.toNat
  have hy := ebcIdx_le y.toNat
  have hx' := x.isLt
  have hy' := y.isLt
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
    omega
  · intro h
    rw [h]

theorem ebc_toInt (x : JChar) : (BitVec.ofNat 32 (ebcIdx x.toNat)).toInt = ebcIdx x.toNat := by
  have hx := ebcIdx_le x.toNat
  have hx' := x.isLt
  have := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 (ebcIdx x.toNat))
  simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
  split at this <;> omega

end EquivLean.Modernize.Cbstm03a.Java
