import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-!
# Arithmetic facts for the numeric helpers

`long` values of `|v|` (`v ≠ Long.MIN_VALUE`), remainders by `10 ^ k` (`pow10`'s result as the simp normal
form `10#64 ^ k`), the last digits `zpadStr (c % 10 ^ m) m = zpadStr c m`, and `trunc11`'s two cases.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (zpadStr digitChar msb_false_of_toInt_nonneg)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem toNat_of_nonneg64 (x : BitVec 64) (h : 0 ≤ x.toInt) : (x.toNat : Int) = x.toInt := by
  have := BitVec.toInt_eq_toNat_cond x
  split at this <;> omega

theorem natAbs_eq_toNat (x : BitVec 64) (h : 0 ≤ x.toInt) : x.toInt.natAbs = x.toNat := by
  have h1 := toNat_of_nonneg64 x h
  have h2 := Int.natAbs_of_nonneg h
  omega

/-- `-v` for `v ≠ Long.MIN_VALUE`. -/
theorem neg_toInt (x : BitVec 64) (h : -9223372036854775808 < x.toInt) : (-x).toInt = -x.toInt :=
  BitVec.toInt_neg_of_not_negOverflow (by simp [BitVec.negOverflow]; omega)

theorem natAbs_eq_neg_toNat (x : BitVec 64) (h : x.toInt < 0) (h' : -9223372036854775808 < x.toInt) :
    x.toInt.natAbs = (-x).toNat := by
  have h1 := neg_toInt x h'
  have h2 := toNat_of_nonneg64 (-x) (by omega)
  have h3 := Int.ofNat_natAbs_of_nonpos (show x.toInt ≤ 0 by omega)
  omega

theorem pow10_eq (k : Nat) : (10#64 : BitVec 64) ^ k = BitVec.ofNat 64 (10 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BitVec.pow_succ, ih]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.pow_succ, Nat.mod_mul_mod]

theorem pow10_toNat (k : Nat) (hk : k < 20) : ((10#64 : BitVec 64) ^ k).toNat = 10 ^ k := by
  rw [pow10_eq, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : 10 ^ k ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem pow10_toInt (k : Nat) (hk : k < 19) : ((10#64 : BitVec 64) ^ k).toInt = 10 ^ k := by
  have h1 := pow10_toNat k (by omega)
  have : 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 := BitVec.toInt_eq_toNat_cond ((10#64 : BitVec 64) ^ k)
  rw [h1] at h2
  split at h2
  · rw [h2]; norm_cast
  · omega

theorem pow10_ne_zero (k : Nat) (hk : k < 20) : ¬ ((10#64 : BitVec 64) ^ k = 0#64) := fun h => by
  have h1 := pow10_toNat k hk
  rw [h] at h1
  simp at h1

theorem num_srem_toNat_of_nonneg (x m : BitVec 64) (hx : 0 ≤ x.toInt) (hm : 0 ≤ m.toInt) :
    (x.srem m).toNat = x.toNat % m.toNat := by
  rw [BitVec.srem_eq, msb_false_of_toInt_nonneg x hx, msb_false_of_toInt_nonneg m hm]
  simp [BitVec.toNat_umod]

theorem srem_nonneg (x m : BitVec 64) (hx : 0 ≤ x.toInt) (hm : 0 ≤ m.toInt) : 0 ≤ (x.srem m).toInt := by
  rw [BitVec.toInt_srem]
  exact Int.tmod_nonneg _ hx

/-- The last `m` digits of `c` are those of `c % 10 ^ m`. -/
theorem zpadStr_modN : ∀ (m c : Nat), zpadStr (c % 10 ^ m) m = zpadStr c m
  | 0, _ => rfl
  | m + 1, c => by
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 :=
      Nat.mod_mod_of_dvd c ⟨10 ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    simp only [zpadStr, h1, h2, zpadStr_modN m (c / 10)]

/-- `zeroPad(a % pow10(k), k)` for `a ≥ 0`, `k < 19`: the last `k` digits of `a`. -/
theorem zpad_srem (x : BitVec 64) (hx : 0 ≤ x.toInt) (k : Nat) (hk : k < 19) :
    zpadStr (x.srem ((10#64 : BitVec 64) ^ k)).toNat k = zpadStr x.toNat k := by
  rw [num_srem_toNat_of_nonneg x _ hx (by rw [pow10_toInt k hk]; positivity), pow10_toNat k (by omega), zpadStr_modN]

theorem srem_pow10_nonneg (x : BitVec 64) (hx : 0 ≤ x.toInt) (k : Nat) (hk : k < 19) :
    0 ≤ x.toInt.tmod ((10#64 : BitVec 64) ^ k).toInt :=
  Int.tmod_nonneg _ hx

theorem c11_toInt : (100000000000#64 : BitVec 64).toInt = 100000000000 := by decide

theorem trunc11_pos (w : BitVec 64) (h : ¬ w.toInt < 0) :
    w.srem 100000000000#64 = BitVec.ofInt 64 (trunc11Z w.toInt) := by
  have ha := Int.natAbs_of_nonneg (show 0 ≤ w.toInt by omega)
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, c11_toInt, Int.tmod_eq_emod_of_nonneg (by omega), trunc11Z, if_neg h,
    BitVec.toInt_ofInt_eq_self (by decide) (by simp only [Nat.reduceSub, Int.reducePow]; omega)
      (by simp only [Nat.reduceSub, Int.reducePow]; omega)]
  omega

theorem trunc11_neg (w : BitVec 64) (h : w.toInt < 0) (h' : -9223372036854775808 < w.toInt) :
    -BitVec.srem (-w) 100000000000#64 = BitVec.ofInt 64 (trunc11Z w.toInt) := by
  have ha := Int.ofNat_natAbs_of_nonpos (show w.toInt ≤ 0 by omega)
  have hn := neg_toInt w h'
  have hs : (BitVec.srem (-w) 100000000000#64).toInt = (-w.toInt) % 100000000000 := by
    rw [BitVec.toInt_srem, c11_toInt, hn, Int.tmod_eq_emod_of_nonneg (by omega)]
  have hs0 : 0 ≤ (-w.toInt) % 100000000000 := Int.emod_nonneg _ (by decide)
  have hs1 : (-w.toInt) % 100000000000 < 100000000000 := Int.emod_lt_of_pos _ (by decide)
  apply BitVec.eq_of_toInt_eq
  rw [neg_toInt _ (by omega), hs, trunc11Z, if_pos h,
    BitVec.toInt_ofInt_eq_self (by decide) (by simp only [Nat.reduceSub, Int.reducePow]; omega)
      (by simp only [Nat.reduceSub, Int.reducePow]; omega)]
  omega

end EquivLean.Modernize.Cbstm03a.Java
