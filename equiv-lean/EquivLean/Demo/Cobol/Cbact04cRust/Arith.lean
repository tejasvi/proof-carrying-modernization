import EquivLean.Demo.Cobol.Cbact04c.All

/-!
# Rust `i64` arithmetic on integers = CBACT04C's COBOL arithmetic

Within the field bounds the checked `i64` operations of the Rust code are exact (`run_eq`),
so its arithmetic is integer arithmetic with `Int.tdiv` and `Int.tmod` (Rust's `/` and `%`:
truncation toward zero).  Against coblean's `divRound .truncation` and `Sem.fitNum` (high-order
truncation of a `PIC S9(n)V99` result) this needs no bounds at all.  The first lemmas are those
of `EquivLean.Demo.Cbact04c` (`Demo/Jimple/Cbact04c/Arith.lean`), restated here so that the
Rust proof does not import the Java side.
-/

open Cobol CardDemo.Cbact04c

namespace EquivLean.Demo.Cbact04cRust

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

theorem fitNum_monthly (v : Int) : (Sem.fitNum {} WS_MONTHLY_INT.fmt v).2 = v.tmod (10 ^ 11) := by
  rw [← fitDec_eq_tmod]; rfl

theorem fitNum_total (v : Int) : (Sem.fitNum {} WS_TOTAL_INT.fmt v).2 = v.tmod (10 ^ 11) := by
  rw [← fitDec_eq_tmod]; rfl

theorem fitNum_bal (v : Int) : (Sem.fitNum {} ACCT_CURR_BAL.fmt v).2 = v.tmod (10 ^ 12) := by
  rw [← fitDec_eq_tmod]; rfl

theorem p11 : (10 : Int) ^ 11 = 100000000000 := by decide
theorem p12 : (10 : Int) ^ 12 = 1000000000000 := by decide

/-- One category: the Rust update of `total_int` (`(total + bal * rate / 120000 % 10^11) % 10^11`
on integers) is coblean's `addInt` step (`COMPUTE WS-MONTHLY-INT`, `ADD … TO WS-TOTAL-INT`). -/
theorem rtotal_step (T b r : Int) :
    (T + ((b * r).tdiv 120000).tmod 100000000000).tmod 100000000000 =
      (Sem.fitNum {} WS_TOTAL_INT.fmt
        (T + (Sem.fitNum {} WS_MONTHLY_INT.fmt (Cobol.divRound .truncation (b * r) 120000)).2)).2 := by
  rw [fitNum_total, fitNum_monthly, divRound_truncation_eq_tdiv _ _ (by decide), p11]

/-- Posting: the Rust balance (`% 10^12`) is coblean's `S9(10)V99` balance. -/
theorem rpost_bal (bal t : Int) :
    (bal + t).tmod 1000000000000 = (Sem.fitNum {} ACCT_CURR_BAL.fmt (bal + t)).2 := by
  rw [fitNum_bal, p12]

end EquivLean.Demo.Cbact04cRust
