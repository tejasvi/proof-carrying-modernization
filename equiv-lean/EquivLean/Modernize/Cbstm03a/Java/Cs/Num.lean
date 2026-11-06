import EquivLean.Modernize.Cbstm03a.Java.Cs.Base

/-!
# CBSTM03A → Java: `createStatement`, the current balance's text

`Iface1`'s `decodeZoned` and `fmtCurrBal` texts against `Iface3`'s: `zonedVal = decodeZonedI` (`zonedVal_eq`), the
value of a 12-character zoned text is below `10 ^ 12` (so it is its own `long`), and `currStr = fmtCurrBalI`
(`currStr_eq`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (fixStr zpadStr digitChar space)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

/-! ## `fmtCurrBal` -/

theorem zpadStr_modN (c : Nat) : ∀ m, zpadStr c m = zpadStr (c % 10 ^ m) m
  | 0 => rfl
  | m + 1 => by
    show zpadStr (c / 10) m ++ [digitChar (c % 10)] =
      zpadStr (c % 10 ^ (m + 1) / 10) m ++ [digitChar (c % 10 ^ (m + 1) % 10)]
    rw [zpadStr_modN (c / 10) m, zpadStr_modN (c % 10 ^ (m + 1) / 10) m]
    have h1 : c % 10 ^ (m + 1) / 10 % 10 ^ m = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, Nat.mod_mod]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 :=
      Nat.mod_mod_of_dvd c (Dvd.intro_left _ (Nat.pow_succ 10 m).symm)
    rw [h1, h2]

theorem currStr_eq (v : Int) : currStr v = fmtCurrBalI v := by
  unfold currStr fmtCurrBalI
  have h1 : zpadStr (v.natAbs / 100) 9 = zpadStr (v.natAbs % 100000000000 / 100) 9 := by
    rw [zpadStr_modN (v.natAbs / 100) 9, zpadStr_modN (v.natAbs % 100000000000 / 100) 9,
      show (10 : Nat) ^ 9 = 1000000000 from rfl]
    congr 1
    omega
  have h2 : zpadStr v.natAbs 2 = zpadStr (v.natAbs % 100000000000 % 100) 2 := by
    rw [zpadStr_modN v.natAbs 2, zpadStr_modN (v.natAbs % 100000000000 % 100) 2,
      show (10 : Nat) ^ 2 = 100 from rfl]
    congr 1
    omega
  have h3 : JStr.ofString "." = [chDot] := rfl
  have h4 : signStr v = [if v < 0 then chDash else space] := by
    unfold signStr
    split <;> rfl
  rw [h1, h2, h3, h4]

/-! ## `decodeZoned` -/

theorem zLast_lt (c : JChar) (neg : Bool) : (zLast c neg).1 < 10 := by
  unfold zLast lowDigit
  split_ifs <;> simp only <;> omega

theorem zAcc_lt (s : JStr) : ∀ i, (zAcc s i).1 < 10 ^ i
  | 0 => by simp [zAcc]
  | i + 1 => by
    have ih := zAcc_lt s i
    have hp : 10 ^ (i + 1) = 10 ^ i * 10 := Nat.pow_succ 10 i
    simp only [zAcc]
    split_ifs
    · simp only; omega
    · have := zLast_lt (s.getD i 0) (zAcc s i).2
      simp only; omega
    · have : lowDigit (s.getD i 0) < 10 := by unfold lowDigit; omega
      simp only; omega

theorem zonedVal_natAbs_lt (s : JStr) : (zonedVal s).natAbs < 10 ^ s.length := by
  unfold zonedVal
  have := zAcc_lt s s.length
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega

/-- The value of a 12-character zoned text is its own `long`. -/
theorem toInt_ofInt_zoned {s : JStr} (h : s.length = 12) :
    (BitVec.ofInt 64 (zonedVal s)).toInt = zonedVal s := by
  have hb := zonedVal_natAbs_lt s
  rw [h, show (10 : Nat) ^ 12 = 1000000000000 from rfl] at hb
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 from rfl]
    omega
  · rw [show (2 : Int) ^ (64 - 1) = 9223372036854775808 from rfl]
    omega

theorem zAcc_prefix (t : JStr) (c : JChar) :
    ∀ i, i ≤ t.length → zAcc (t ++ [c]) i = ((t.take i).foldl (fun v d => v * 10 + zdig d) 0, false)
  | 0, _ => by simp [zAcc]
  | i + 1, h => by
    have hi : i < t.length := h
    have ih := zAcc_prefix t c i (Nat.le_of_lt hi)
    have hg : (t ++ [c]).getD i 0 = t.getD i 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have hlen : ¬ (i + 1 = (t ++ [c]).length) := by rw [List.length_append, List.length_singleton]; omega
    have hf : (t.take (i + 1)).foldl (fun v d => v * 10 + zdig d) 0 =
        (t.take i).foldl (fun v d => v * 10 + zdig d) 0 * 10 + zdig (t.getD i 0) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some]
    simp only [zAcc, ih, hg, hlen, hf, if_false]
    split_ifs with hd
    · simp only [Prod.mk.injEq, and_true]
      unfold zdig
      omega
    · rfl

theorem zlast_eq (c : JChar) (hd : ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) : zlast c = zLast c false := by
  unfold zlast zLast
  rw [if_neg hd]
  rfl

theorem zonedVal_eq (s : JStr) : zonedVal s = decodeZonedI s := by
  rcases List.eq_nil_or_concat s with rfl | ⟨t, c, rfl⟩
  · rfl
  · simp only [List.concat_eq_append]
    have hL : (t ++ [c]).length = t.length + 1 := by simp
    have hgc : (t ++ [c]).getD t.length 0 = c := by simp [List.getD_eq_getElem?_getD]
    have hpre := zAcc_prefix t c t.length (Nat.le_refl _)
    rw [List.take_of_length_le (Nat.le_refl _)] at hpre
    have hlast : (t ++ [c]).getLast? = some c := by simp
    have hdrop : (t ++ [c]).dropLast = t := by simp
    unfold zonedVal decodeZonedI
    rw [hL, hlast, hdrop]
    simp only [zAcc, hpre, hgc]
    by_cases hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57
    · have hz : zlast c = (c.toNat - 48, false) := by unfold zlast; rw [if_pos hd]
      simp only [if_pos hd, hz] <;> rfl
    · rw [zlast_eq c hd]
      simp only [if_neg hd, hL, ↓reduceIte] <;> rfl

end EquivLean.Modernize.Cbstm03a.Java.Cs
