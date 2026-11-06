import EquivLean.Demo.Cobol.Cbact04c.All
import EquivLean.Demo.Jimple.Cbact04c.Model

/-!
# Java `long` arithmetic = CBACT04C's COBOL arithmetic, within the field sizes

`/` and `%` on `long` (`BitVec.sdiv`, `BitVec.srem`: truncation toward zero) against coblean's
`divRound .truncation` and `Sem.fitNum` (high-order truncation of a `PIC S9(n)V99` result).
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

theorem tmod_neg_eq {x m : Int} (hx : x < 0) : x.tmod m = -((-x) % m) := by
  have h := Int.neg_tmod (-x) m
  rw [Int.neg_neg] at h
  rw [h, Int.tmod_eq_emod_of_nonneg (by omega)]

theorem natAbs_cast_eq (v : Int) : (v.natAbs : Int) = if 0 ≤ v then v else -v := by
  split
  · next h => exact Int.natAbs_of_nonneg h
  · next h => exact Int.ofNat_natAbs_of_nonpos (by omega)

theorem fitDec_eq_tmod (n : Nat) (v : Int) : (Sem.fitDec n v).2 = v.tmod (10 ^ n) := by
  unfold Sem.fitDec truncDigits
  have hcast : ((10 ^ n : Nat) : Int) = 10 ^ n := Int.natCast_pow 10 n
  have hp : (0 : Int) < 10 ^ n := Int.pow_pos (by decide)
  have hab := natAbs_cast_eq v
  split
  · next h =>
    have h' : (v.natAbs : Int) < 10 ^ n := by rw [← hcast]; exact Int.ofNat_lt.mpr h
    by_cases hv : 0 ≤ v
    · simp only [hv, ↓reduceIte] at hab
      rw [Int.tmod_eq_emod_of_nonneg hv, Int.emod_eq_of_lt hv (by omega)]
    · simp only [hv, ↓reduceIte] at hab
      rw [tmod_neg_eq (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
      omega
  · next h =>
    simp only
    split
    · next hv => rw [Int.tmod_eq_emod_of_nonneg hv]
    · next hv => rw [tmod_neg_eq (by omega)]

theorem divRound_truncation_eq_tdiv (n d : Int) (_hd : 0 < d) :
    Cobol.divRound .truncation n d = n.tdiv d := by
  show (if 0 ≤ n then n / d else -((-n) / d)) = n.tdiv d
  split
  · next h => rw [Int.tdiv_eq_ediv_of_nonneg h]
  · next h =>
    have h2 := Int.neg_tdiv (-n) d
    rw [Int.neg_neg] at h2
    rw [h2, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- `toInt` of `ofInt` within the signed 64-bit range. -/
theorem toInt_ofInt64 {x : Int} (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x < 2 ^ 63) :
    (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem fitNum_monthly (v : Int) : (Sem.fitNum {} WS_MONTHLY_INT.fmt v).2 = v.tmod (10 ^ 11) := by
  rw [← fitDec_eq_tmod]; rfl

theorem fitNum_total (v : Int) : (Sem.fitNum {} WS_TOTAL_INT.fmt v).2 = v.tmod (10 ^ 11) := by
  rw [← fitDec_eq_tmod]; rfl

theorem fitNum_bal (v : Int) : (Sem.fitNum {} ACCT_CURR_BAL.fmt v).2 = v.tmod (10 ^ 12) := by
  rw [← fitDec_eq_tmod]; rfl

theorem tmod_bound (v : Int) (n : Nat) : (v.tmod (10 ^ n)).natAbs < 10 ^ n := by
  have := fitDec_lt n v
  rwa [fitDec_eq_tmod] at this

theorem bounds_of_natAbs {v : Int} {n : Nat} (h : v.natAbs < n) : -(n : Int) < v ∧ v < n := by
  have := natAbs_cast_eq v
  have h' : (v.natAbs : Int) < n := Int.ofNat_lt.mpr h
  split at this <;> omega

theorem toInt_lit64 (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_ofNat']
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem p11 : (10 : Int) ^ 11 = 100000000000 := by decide
theorem p12 : (10 : Int) ^ 12 = 1000000000000 := by decide

/-- One category: Java's update of `totalInt` (`long` arithmetic) is coblean's `addInt` step. -/
theorem jtotal_step (T b r : Int) (hT : T.natAbs < 100000000000) (hb : b.natAbs < 100000000000)
    (hr : r.natAbs < 1000000) :
    (BitVec.ofInt 64 T + ((BitVec.ofInt 64 b * BitVec.ofInt 64 r).sdiv 120000).srem 100000000000).srem
        100000000000 =
      BitVec.ofInt 64 ((Sem.fitNum {} WS_TOTAL_INT.fmt
        (T + (Sem.fitNum {} WS_MONTHLY_INT.fmt (Cobol.divRound .truncation (b * r) 120000)).2)).2) := by
  apply BitVec.eq_of_toInt_eq
  rw [fitNum_total, fitNum_monthly, divRound_truncation_eq_tdiv _ _ (by decide), p11]
  have hbr : (b * r).natAbs < 100000000000000000 := by
    rw [Int.natAbs_mul]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hb hr) (by decide)
  obtain ⟨hT1, hT2⟩ := bounds_of_natAbs hT
  obtain ⟨hb1, hb2⟩ := bounds_of_natAbs hb
  obtain ⟨hr1, hr2⟩ := bounds_of_natAbs hr
  obtain ⟨hp1, hp2⟩ := bounds_of_natAbs hbr
  have eT : (BitVec.ofInt 64 T).toInt = T := toInt_ofInt64 (by omega) (by omega)
  have eb : (BitVec.ofInt 64 b).toInt = b := toInt_ofInt64 (by omega) (by omega)
  have er : (BitVec.ofInt 64 r).toInt = r := toInt_ofInt64 (by omega) (by omega)
  have e1 : (120000 : BitVec 64).toInt = 120000 := toInt_lit64 120000 (by decide)
  have e2 : (100000000000 : BitVec 64).toInt = 100000000000 := toInt_lit64 100000000000 (by decide)
  have em : (BitVec.ofInt 64 b * BitVec.ofInt 64 r).toInt = b * r := by
    rw [BitVec.toInt_mul, eb, er]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have hq := Int.natAbs_tdiv_le_natAbs (b * r) 120000
  obtain ⟨hq1, hq2⟩ := bounds_of_natAbs (Nat.lt_of_le_of_lt hq hbr)
  have ed : ((BitVec.ofInt 64 b * BitVec.ofInt 64 r).sdiv 120000).toInt = (b * r).tdiv 120000 := by
    rw [BitVec.toInt_sdiv, em, e1]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have es : (((BitVec.ofInt 64 b * BitVec.ofInt 64 r).sdiv 120000).srem 100000000000).toInt =
      ((b * r).tdiv 120000).tmod 100000000000 := by
    rw [BitVec.toInt_srem, ed, e2]
  have hm := tmod_bound ((b * r).tdiv 120000) 11
  rw [show (10 : Nat) ^ 11 = 100000000000 from rfl, p11] at hm
  obtain ⟨hm1, hm2⟩ := bounds_of_natAbs hm
  have ea : (BitVec.ofInt 64 T + ((BitVec.ofInt 64 b * BitVec.ofInt 64 r).sdiv 120000).srem 100000000000).toInt =
      T + ((b * r).tdiv 120000).tmod 100000000000 := by
    rw [BitVec.toInt_add, eT, es]; exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_srem, ea, e2]
  have hf := tmod_bound (T + ((b * r).tdiv 120000).tmod 100000000000) 11
  rw [show (10 : Nat) ^ 11 = 100000000000 from rfl, p11] at hf
  obtain ⟨hf1, hf2⟩ := bounds_of_natAbs hf
  rw [toInt_ofInt64 (by omega) (by omega)]

/-- Posting: Java's new balance (`% 10^12`) is coblean's `S9(10)V99` balance. -/
theorem jpost_bal (bal t : Int) (hb : bal.natAbs < 1000000000000) (ht : t.natAbs < 100000000000) :
    (BitVec.ofInt 64 bal + BitVec.ofInt 64 t).srem 1000000000000 =
      BitVec.ofInt 64 (Sem.fitNum {} ACCT_CURR_BAL.fmt (bal + t)).2 := by
  apply BitVec.eq_of_toInt_eq
  rw [fitNum_bal, p12]
  obtain ⟨hb1, hb2⟩ := bounds_of_natAbs hb
  obtain ⟨ht1, ht2⟩ := bounds_of_natAbs ht
  have eb : (BitVec.ofInt 64 bal).toInt = bal := toInt_ofInt64 (by omega) (by omega)
  have et : (BitVec.ofInt 64 t).toInt = t := toInt_ofInt64 (by omega) (by omega)
  have e2 : (1000000000000 : BitVec 64).toInt = 1000000000000 := toInt_lit64 1000000000000 (by decide)
  have ea : (BitVec.ofInt 64 bal + BitVec.ofInt 64 t).toInt = bal + t := by
    rw [BitVec.toInt_add, eb, et]; exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_srem, ea, e2]
  have hf := tmod_bound (bal + t) 12
  rw [show (10 : Nat) ^ 12 = 1000000000000 from rfl, p12] at hf
  obtain ⟨hf1, hf2⟩ := bounds_of_natAbs hf
  rw [toInt_ofInt64 (by omega) (by omega)]

/-- A rate within `S9(4)V99` is zero as a `long` iff it is zero. -/
theorem ofInt64_eq_zero_iff (r : Int) (hr : r.natAbs < 1000000) : BitVec.ofInt 64 r = 0 ↔ r = 0 := by
  obtain ⟨h1, h2⟩ := bounds_of_natAbs hr
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    rw [toInt_ofInt64 (by omega) (by omega)] at this
    simpa using this
  · intro h; subst h; rfl

/-- Two account keys (`PIC 9(11)`) are equal as `long`s iff they are equal. -/
theorem ofInt64_inj {x y : Int} (hx : x.natAbs < 100000000000) (hy : y.natAbs < 100000000000) :
    BitVec.ofInt 64 x = BitVec.ofInt 64 y ↔ x = y := by
  obtain ⟨hx1, hx2⟩ := bounds_of_natAbs hx
  obtain ⟨hy1, hy2⟩ := bounds_of_natAbs hy
  constructor
  · intro h
    have := congrArg BitVec.toInt h
    rwa [toInt_ofInt64 (by omega) (by omega), toInt_ofInt64 (by omega) (by omega)] at this
  · intro h; rw [h]

theorem ofNat32_succ (n : Nat) : BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

end EquivLean.Demo.Cbact04c
