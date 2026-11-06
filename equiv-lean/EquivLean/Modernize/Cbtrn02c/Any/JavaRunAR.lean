import EquivLean.Modernize.Cbtrn02c.Any.JavaRunU

/-!
# CBTRN02C → Java: the arithmetic of the postings

COBOL's `ADD` into a signed DISPLAY item truncates high-order digits (`Sem.fitNum` = `Int.tmod`);
Java's `(a + b) % 10^n` on `long`s computes the same when there is no overflow.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem truncDigits_eq_tmod (v : Int) (n : Nat) : Cobol.truncDigits v n = v.tmod (10 ^ n) := by
  unfold Cobol.truncDigits
  split
  · next h => rw [Int.tmod_eq_emod_of_nonneg h]
  · next h =>
    have h' : 0 ≤ -v := by omega
    have := Int.neg_tmod (-v) (10 ^ n)
    rw [Int.neg_neg] at this
    rw [this, Int.tmod_eq_emod_of_nonneg h']

theorem natAbs_bounds {x : Int} {n : Nat} (h : x.natAbs < n) : -(n : Int) < x ∧ x < n := by
  rcases Int.lt_or_le x 0 with hx | hx
  · have := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hx); omega
  · have := Int.natAbs_of_nonneg hx; omega

theorem tmod_eq_self {v m : Int} (h : (v.natAbs : Int) < m) : v.tmod m = v := by
  rcases Int.lt_or_le v 0 with hv | hv
  · have hn : (v.natAbs : Int) = -v := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hv)
    have h' : 0 ≤ -v := by omega
    have e := Int.neg_tmod (-v) m
    rw [Int.neg_neg] at e
    rw [e, Int.tmod_eq_emod_of_nonneg h', Int.emod_eq_of_lt h' (by omega), Int.neg_neg]
  · have hn : (v.natAbs : Int) = v := Int.natAbs_of_nonneg hv
    rw [Int.tmod_eq_emod_of_nonneg hv, Int.emod_eq_of_lt hv (by omega)]

theorem fitNum_signed_display {f : Cobol.NumFmt} (hs : f.signed = true) (hu : f.usage = .display)
    (v : Int) : (Cobol.Sem.fitNum {} f v).2 = v.tmod (10 ^ f.digits) := by
  unfold Cobol.Sem.fitNum
  have hb : f.fullBinary {} = false := by unfold Cobol.NumFmt.fullBinary; simp [hu]
  simp only [hs, ↓reduceIte, hb, Bool.false_eq_true]
  unfold Cobol.Sem.fitDec
  split
  · next h =>
    show v = v.tmod (10 ^ f.digits)
    exact (tmod_eq_self (by exact_mod_cast h)).symm
  · rw [truncDigits_eq_tmod]

theorem toInt_ofInt64 {x : Int} (h : x.natAbs < 9223372036854775808) : (BitVec.ofInt 64 x).toInt = x := by
  have hb := natAbs_bounds h
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  split <;> omega

/-- Java's `(a + b) % m` on `long`s holding small values. -/
theorem srem_add_ofInt (x y : Int) (m : Nat) (hm0 : 0 < m) (hm : m < 9223372036854775808)
    (hx : x.natAbs < 1000000000000000000) (hy : y.natAbs < 1000000000000000000) :
    (BitVec.ofInt 64 x + BitVec.ofInt 64 y).srem (BitVec.ofNat 64 m) =
      BitVec.ofInt 64 ((x + y).tmod m) := by
  apply BitVec.eq_of_toInt_eq
  have hbx := natAbs_bounds hx
  have hby := natAbs_bounds hy
  have hadd : (BitVec.ofInt 64 x + BitVec.ofInt 64 y).toInt = x + y := by
    rw [BitVec.toInt_add, toInt_ofInt64 (by omega), toInt_ofInt64 (by omega), Int.bmod_def]
    split <;> omega
  have hmi : (BitVec.ofNat 64 m).toInt = m := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  rw [BitVec.toInt_srem, hadd, hmi]
  have hb : ((x + y).tmod m).natAbs < 9223372036854775808 := by
    rw [Int.natAbs_tmod]
    exact Nat.lt_trans (Nat.mod_lt _ hm0) hm
  rw [toInt_ofInt64 hb]

end EquivLean.Modernize.Cbtrn02c.Java
