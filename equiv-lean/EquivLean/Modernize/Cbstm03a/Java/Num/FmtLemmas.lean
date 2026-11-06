import EquivLean.Modernize.Cbstm03a.Java.Num.NumLemmas

/-! # The amount texts: `fmtCurrBal`'s and `fmtZ`'s parts -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (zpadStr digitChar msb_false_of_toInt_nonneg)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem num_sdiv_toNat_of_nonneg (x m : BitVec 64) (hx : 0 ≤ x.toInt) (hm : 0 ≤ m.toInt) :
    (x.sdiv m).toNat = x.toNat / m.toNat := by
  rw [BitVec.sdiv_eq, msb_false_of_toInt_nonneg x hx, msb_false_of_toInt_nonneg m hm]
  simp [BitVec.toNat_udiv]

/-- `a = |v| % 10^11`: `a / 100` and `a % 100`. -/
theorem curr_parts (x : BitVec 64) (hx : 0 ≤ x.toInt) :
    ((x.srem 100000000000#64).sdiv 100#64).toNat = x.toNat / 100 % 1000000000 ∧
    ((x.srem 100000000000#64).srem 100#64).toNat = x.toNat % 100 := by
  have h11 : (0 : Int) ≤ (100000000000#64 : BitVec 64).toInt := by decide
  have h100 : (0 : Int) ≤ (100#64 : BitVec 64).toInt := by decide
  have hs := srem_nonneg x 100000000000#64 hx h11
  have ht := num_srem_toNat_of_nonneg x 100000000000#64 hx h11
  rw [num_sdiv_toNat_of_nonneg _ _ hs h100, num_srem_toNat_of_nonneg _ _ hs h100, ht]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem zpad9 (c : Nat) : zpadStr (c % 1000000000) 9 = zpadStr c 9 := by
  have := zpadStr_modN 9 c
  simpa using this

theorem zpad2 (c : Nat) : zpadStr (c % 100) 2 = zpadStr c 2 := by
  have := zpadStr_modN 2 c
  simpa using this

theorem dot_cons (l : JStr) : JStr.ofString "." ++ l = 46#16 :: l := rfl

theorem currStr_eq (v : Int) (c : Nat) (hc : c = v.natAbs) (sgn : JStr) (hs : sgn = signStr v) :
    zpadStr (c / 100 % 1000000000) 9 ++ 46#16 :: (zpadStr (c % 100) 2 ++ sgn) = currStr v := by
  subst hc hs
  rw [zpad9, zpad2]
  simp only [currStr, List.append_assoc, dot_cons, List.cons_append]

theorem currStr_neg (w : BitVec 64) (h : w.toInt < 0) (h' : -9223372036854775808 < w.toInt) :
    zpadStr ((BitVec.srem (-w) 100000000000#64).sdiv 100#64).toNat 9 ++
      46#16 :: (zpadStr ((BitVec.srem (-w) 100000000000#64).srem 100#64).toNat 2 ++ JStr.ofString "-") =
    currStr w.toInt := by
  obtain ⟨h1, h2⟩ := curr_parts (-w) (by rw [neg_toInt _ h']; omega)
  rw [h1, h2]
  exact currStr_eq _ _ (natAbs_eq_neg_toNat w h h').symm _ (by simp [signStr, h])

theorem currStr_pos (w : BitVec 64) (h : ¬ w.toInt < 0) :
    zpadStr ((BitVec.srem w 100000000000#64).sdiv 100#64).toNat 9 ++
      46#16 :: (zpadStr ((BitVec.srem w 100000000000#64).srem 100#64).toNat 2 ++ JStr.ofString " ") =
    currStr w.toInt := by
  obtain ⟨h1, h2⟩ := curr_parts w (by omega)
  rw [h1, h2]
  exact currStr_eq _ _ (natAbs_eq_toNat w (by omega)).symm _ (by simp [signStr, h])

end EquivLean.Modernize.Cbstm03a.Java
