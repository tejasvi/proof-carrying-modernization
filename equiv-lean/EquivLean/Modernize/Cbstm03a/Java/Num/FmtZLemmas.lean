import EquivLean.Modernize.Cbstm03a.Java.Num.FmtLemmas
import EquivLean.Modernize.Cbstm03a.Java.Num.Lead0

/-! # `fmtZ`'s closing facts -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (zpadStr digitChar zpadStr_length space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem srem11_toNat_neg (w : BitVec 64) (h : w.toInt < 0) (h' : -9223372036854775808 < w.toInt) :
    (BitVec.srem (-w) 100000000000#64).toNat = w.toInt.natAbs % 100000000000 := by
  rw [num_srem_toNat_of_nonneg _ _ (by rw [neg_toInt _ h']; omega) (by decide), natAbs_eq_neg_toNat w h h']
  simp

theorem srem11_toNat_pos (w : BitVec 64) (h : ¬ w.toInt < 0) :
    (BitVec.srem w 100000000000#64).toNat = w.toInt.natAbs % 100000000000 := by
  rw [num_srem_toNat_of_nonneg _ _ (by omega) (by decide), natAbs_eq_toNat w (by omega)]
  simp

theorem ip_neg (w : BitVec 64) (h : w.toInt < 0) (h' : -9223372036854775808 < w.toInt) :
    zpadStr ((BitVec.srem (-w) 100000000000#64).sdiv 100#64).toNat 9 = zpadStr (w.toInt.natAbs / 100) 9 := by
  rw [(curr_parts (-w) (by rw [neg_toInt _ h']; omega)).1, zpad9, natAbs_eq_neg_toNat w h h']

theorem ip_pos (w : BitVec 64) (h : ¬ w.toInt < 0) :
    zpadStr ((BitVec.srem w 100000000000#64).sdiv 100#64).toNat 9 = zpadStr (w.toInt.natAbs / 100) 9 := by
  rw [(curr_parts w (by omega)).1, zpad9, natAbs_eq_toNat w (by omega)]

theorem lead0_step' (s : JStr) (k : Int) (c : JChar) (hk0 : 0 ≤ k) (hk : k.toNat ≤ lead0 s)
    (hd : s[k.toNat]? = some c) (hc : BitVec.setWidth 32 c = 48#32) : k + 1 ≤ (lead0 s : Int) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hd
  have := lead0_step s k.toNat hk hlt (by rw [hget]; exact (char48_iff c).1 hc)
  omega

theorem lead0_stop' (s : JStr) (k : Int) (c : JChar) (hk : k.toNat ≤ lead0 s)
    (hd : s[k.toNat]? = some c) (hc : ¬ BitVec.setWidth 32 c = 48#32) : lead0 s = k.toNat := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hd
  exact lead0_stop s k.toNat hk hlt (by rw [hget]; exact fun e => hc ((char48_iff c).2 e))

theorem signStr_pos (v : Int) (h : 0 ≤ v) : JStr.ofString " " = signStr v := by
  simp [signStr, show ¬ v < 0 by omega]

theorem signStr_neg (v : Int) (h : ¬ 0 ≤ v) : JStr.ofString "-" = signStr v := by
  simp [signStr, show v < 0 by omega]

theorem fmtZ_close (v : Int) (k : Nat) (hk : k = lead0 (zpadStr (v.natAbs / 100) 9)) (a : BitVec 64)
    (ha0 : 0 ≤ a.toInt) (ha : a.toNat = v.natAbs % 100000000000) (sgn : JStr) (hs : sgn = signStr v) :
    List.replicate k space ++ (List.drop k (zpadStr (v.natAbs / 100) 9) ++
      46#16 :: (zpadStr (BitVec.srem a 100#64).toNat 2 ++ sgn)) = fmtZStr v := by
  have h1 : (BitVec.srem a 100#64).toNat = v.natAbs % 100000000000 % 100 := by
    rw [num_srem_toNat_of_nonneg _ _ ha0 (by decide), ha]
    simp
  have h2 : v.natAbs % 100000000000 % 100 = v.natAbs % 100 := by omega
  rw [h1, h2, zpad2]
  subst hk hs
  simp only [fmtZStr, List.append_assoc, dot_cons, List.cons_append]

end EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java

theorem lead0_step2 (s : JStr) (k : Int) (hk0 : 0 ≤ k) (hk : k.toNat ≤ lead0 s) (hlt : k.toNat < s.length)
    (hc : BitVec.setWidth 32 s[k.toNat] = 48#32) : k + 1 ≤ (lead0 s : Int) := by
  have := lead0_step s k.toNat hk hlt ((char48_iff _).1 hc)
  omega

theorem lead0_stop2 (s : JStr) (k : Int) (hk : k.toNat ≤ lead0 s) (hlt : k.toNat < s.length)
    (hc : ¬ BitVec.setWidth 32 s[k.toNat] = 48#32) : k.toNat = lead0 s :=
  (lead0_stop s k.toNat hk hlt (fun e => hc ((char48_iff _).2 e))).symm

end EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java

theorem fmtZ_stop_pos (v k : Int) (a : BitVec 64) (c : JChar) (hv : 0 ≤ v)
    (hk : k.toNat ≤ lead0 (zpadStr (v.natAbs / 100) 9)) (hd : (zpadStr (v.natAbs / 100) 9)[k.toNat]? = some c)
    (hc : ¬ BitVec.setWidth 32 c = 48#32) (ha0 : 0 ≤ a.toInt) (ha : a.toNat = v.natAbs % 100000000000) :
    List.replicate k.toNat space ++ (List.drop k.toNat (zpadStr (v.natAbs / 100) 9) ++
      46#16 :: (zpadStr (BitVec.srem a 100#64).toNat 2 ++ JStr.ofString " ")) = fmtZStr v :=
  fmtZ_close v k.toNat (lead0_stop' _ _ _ hk hd hc).symm a ha0 ha _ (signStr_pos v hv)

theorem fmtZ_stop_neg (v k : Int) (a : BitVec 64) (c : JChar) (hv : ¬ 0 ≤ v)
    (hk : k.toNat ≤ lead0 (zpadStr (v.natAbs / 100) 9)) (hd : (zpadStr (v.natAbs / 100) 9)[k.toNat]? = some c)
    (hc : ¬ BitVec.setWidth 32 c = 48#32) (ha0 : 0 ≤ a.toInt) (ha : a.toNat = v.natAbs % 100000000000) :
    List.replicate k.toNat space ++ (List.drop k.toNat (zpadStr (v.natAbs / 100) 9) ++
      46#16 :: (zpadStr (BitVec.srem a 100#64).toNat 2 ++ JStr.ofString "-")) = fmtZStr v :=
  fmtZ_close v k.toNat (lead0_stop' _ _ _ hk hd hc).symm a ha0 ha _ (signStr_neg v hv)

end EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java

theorem lead0_nine (v k : Int) (hk9 : k = 9) (hk : k.toNat ≤ lead0 (zpadStr (v.natAbs / 100) 9)) :
    9 = lead0 (zpadStr (v.natAbs / 100) 9) :=
  (lead0_full _ 9 (by omega) (by simp [zpadStr_length])).symm

theorem fmtZ_nine_pos (v k : Int) (a : BitVec 64) (hv : 0 ≤ v) (hk9 : k = 9)
    (hk : k.toNat ≤ lead0 (zpadStr (v.natAbs / 100) 9)) (ha0 : 0 ≤ a.toInt) (ha : a.toNat = v.natAbs % 100000000000) :
    space :: space :: space :: space :: space :: space :: space :: space :: space ::
      (List.drop 9 (zpadStr (v.natAbs / 100) 9) ++
        46#16 :: (zpadStr (BitVec.srem a 100#64).toNat 2 ++ JStr.ofString " ")) = fmtZStr v :=
  fmtZ_close v 9 (lead0_nine v k hk9 hk) a ha0 ha _ (signStr_pos v hv)

theorem fmtZ_nine_neg (v k : Int) (a : BitVec 64) (hv : ¬ 0 ≤ v) (hk9 : k = 9)
    (hk : k.toNat ≤ lead0 (zpadStr (v.natAbs / 100) 9)) (ha0 : 0 ≤ a.toInt) (ha : a.toNat = v.natAbs % 100000000000) :
    space :: space :: space :: space :: space :: space :: space :: space :: space ::
      (List.drop 9 (zpadStr (v.natAbs / 100) 9) ++
        46#16 :: (zpadStr (BitVec.srem a 100#64).toNat 2 ++ JStr.ofString "-")) = fmtZStr v :=
  fmtZ_close v 9 (lead0_nine v k hk9 hk) a ha0 ha _ (signStr_neg v hv)

end EquivLean.Modernize.Cbstm03a.Java
