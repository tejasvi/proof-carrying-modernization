import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.AcctInt.Funs

/-!
# The Rust side of ACCTINT: specification of `acctint.accrue` on the COBOL domain

`acctint.accrue` (`examples/rust/acctint/src/lib.rs`, the scaled-integer rewrite of
`ACCTINT.cob`, translated by Charon + Aeneas) is described by `accrueModel`, a function on
mathematical integers that follows the Rust code: `accrue_spec` / `accrue_equiv_model`.  The
hypotheses are the COBOL field ranges: `ACCT-BALANCE PIC S9(11)V99` (`|balance| ≤ 10^13`
cents) and `ACCT-RATE PIC SV9(5)` (`|rate| ≤ 10^5` units of `10^-5`); `days` is any `u16`.
On this domain the Rust function never panics (no `i128` overflow).

* `wp_div_half_up`: a call specification for `div_half_up`.  Inlining both calls into
  `accrue` makes the symbolic execution too large for `simp` (100000 steps), so `accrue` is
  executed with the calls folded and each call is rewritten with this lemma.
* `divHalfUp`: `n / d` rounded half away from zero (`d > 0`), on `Int`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.Aeneas.AcctInt

/-- `n / d` rounded half away from zero, for `d > 0`: Rust's `div_half_up` in `Int`. -/
def divHalfUp (n d : Int) : Int :=
  if 0 ≤ n then (2 * n + d) / (2 * d) else -((2 * -n + d) / (2 * d))

theorem divHalfUp_bounds (n d : Int) (hd : 0 < d) :
    -(2 * |n| + d) ≤ divHalfUp n d ∧ divHalfUp n d ≤ 2 * |n| + d := by
  unfold divHalfUp
  split
  · next hn =>
    have h1 := Int.ediv_nonneg (a := 2 * n + d) (b := 2 * d) (by omega) (by omega)
    have h2 := Int.ediv_le_self (2 * d) (a := 2 * n + d) (by omega)
    rw [abs_of_nonneg hn]; omega
  · next hn =>
    have h1 := Int.ediv_nonneg (a := 2 * -n + d) (b := 2 * d) (by omega) (by omega)
    have h2 := Int.ediv_le_self (2 * d) (a := 2 * -n + d) (by omega)
    rw [abs_of_neg (by omega)]; omega

theorem divHalfUp_inRange (n d : Int) (hd : 0 < d) (hn : -2 ^ 120 ≤ n ∧ n ≤ 2 ^ 120)
    (hd' : d ≤ 2 ^ 120) :
    -2 ^ (IScalarTy.I128.numBits - 1) ≤ divHalfUp n d ∧
      divHalfUp n d < 2 ^ (IScalarTy.I128.numBits - 1) := by
  have := divHalfUp_bounds n d hd
  have habs : |n| ≤ 2 ^ 120 := abs_le.2 ⟨by omega, hn.2⟩
  simp only [IScalarTy.I128_numBits_eq]
  omega

/-- A call of `div_half_up` returns the half-away-from-zero quotient (no panic) when the
divisor is positive and both arguments are below `2^120` in absolute value. -/
theorem wp_div_half_up (n d : I128) (Q : Except Error I128 → Prop) (hd : 0 < d.val)
    (hn : -2 ^ 120 ≤ n.val ∧ n.val ≤ 2 ^ 120) (hd' : d.val ≤ 2 ^ 120) :
    wp (acctint.div_half_up n d) Q ↔
      Q (.ok (IScalar.ofIntCore (divHalfUp n.val d.val) (divHalfUp_inRange _ _ hd hn hd'))) := by
  aeneas_wp [acctint.div_half_up]
  split_ifs
  all_goals first
    | (exfalso; omega)
    | (have heq : (2 * n.val + d.val).tdiv (2 * d.val) = divHalfUp n.val d.val := by
          rw [divHalfUp, ite_eq_left (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
       simp only [heq])
    | (have heq : -(2 * -n.val + d.val).tdiv (2 * d.val) = divHalfUp n.val d.val := by
          rw [divHalfUp, ite_eq_right (by omega), Int.tdiv_eq_ediv_of_nonneg (by omega)]
       simp only [heq])
    | (exfalso
       have h1 := Int.ediv_nonneg (a := 2 * -n.val + d.val) (b := 2 * d.val) (by omega) (by omega)
       have h2 := Int.ediv_le_self (2 * d.val) (a := 2 * -n.val + d.val) (by omega)
       rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at *
       omega)

def absI (x : Int) : Int := if x < 0 then -x else x

def accrueModel (t : Char) (bal rate : Int) (days : Nat) : Int × Int × Char :=
  if days = 0 ∨ (t ≠ 'S' ∧ t ≠ 'C') then (bal, 0, 'Z')
  else
    let daily := divHalfUp (rate * 1000) 365
    let interest := divHalfUp (bal * daily * days) 100000000
    if 100000000000 ≤ absI interest then (bal, 0, 'E')
    else if 10000000000000 ≤ absI (bal + interest) then (bal, interest, 'E')
    else (bal + interest, interest, 'K')

theorem prod_bound (a b c : Int) (ha : -10^13 ≤ a ∧ a ≤ 10^13)
    (hb : -(2 * 10^8 + 365) ≤ b ∧ b ≤ 2 * 10^8 + 365) (hc : 0 ≤ c ∧ c ≤ 65535) :
    -2^120 ≤ a * b * c ∧ a * b * c ≤ 2^120 ∧ -2^100 ≤ a * b ∧ a * b ≤ 2^100 := by
  have h1 : |a| ≤ 10^13 := abs_le.2 ha
  have h2 : |b| ≤ 2 * 10^8 + 365 := abs_le.2 hb
  have h3 : |c| ≤ 65535 := abs_le.2 ⟨by omega, hc.2⟩
  have hab : |a * b| ≤ 10^13 * (2 * 10^8 + 365) := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  have habc : |a * b * c| ≤ 10^13 * (2 * 10^8 + 365) * 65535 := by
    rw [abs_mul]; exact mul_le_mul hab h3 (abs_nonneg _) (by norm_num)
  have e1 := abs_le.1 hab
  have e2 := abs_le.1 habc
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem cast_I64_ofIntCore (v : Int) (h : -2 ^ (IScalarTy.I128.numBits - 1) ≤ v ∧
      v < 2 ^ (IScalarTy.I128.numBits - 1))
    (h1 : -9223372036854775808 ≤ v) (h2 : v < 9223372036854775808) :
    (IScalar.cast .I64 (IScalar.ofIntCore (ty := .I128) v h)).val = v := by
  rw [IScalar.val_mod_pow_inBounds .I64 _ (by simpa using h1) (by simpa using h2)]
  exact IScalar.ofInt_val_eq h

/-- The Rust function on the COBOL domain: no panic, and the result of `accrueModel`. -/
theorem accrue_spec (t : Char) (b : Option I64) (rate : I64) (days : U16)
    (hb : -10^13 ≤ (core.option.Option.unwrap_or b 0#i64).val ∧
      (core.option.Option.unwrap_or b 0#i64).val ≤ 10^13)
    (hr : -10^5 ≤ rate.val ∧ rate.val ≤ 10^5) :
    wp (acctint.accrue t b rate days) (fun o => ∃ x y c, o = .ok (x, y, c) ∧
      (x.val, y.val, c) = accrueModel t (core.option.Option.unwrap_or b 0#i64).val rate.val days.val) := by
  unfold acctint.accrue
  generalize core.option.Option.unwrap_or b 0#i64 = bal at hb ⊢
  by_cases h0 : days.val = 0
  · have h0' : days = 0#u16 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    simp [h0', accrueModel]
  · have h0' : ¬ days = 0#u16 := fun h => h0 (by rw [h]; rfl)
    by_cases hT : t = 'S' ∨ t = 'C'
    · have c1 : -170141183460469231731687303715884105728 ≤ rate.val * 1000 ∧
          rate.val * 1000 ≤ 170141183460469231731687303715884105727 := by omega
      have hcs : ('C' != 'S') = true := by decide
      have hcc : ('C' != 'C') = false := by decide
      have hss : ('S' != 'S') = false := by decide
      rcases hT with rfl | rfl <;>
      · simp only [lift, bind_ok, h0', ite_false, hcs, hcc, hss, ite_true, Bool.false_eq_true]
        aeneas_wp [core.num.I128.abs, c1]
        rw [wp_div_half_up _ _ _ (by simp) (by simp; omega) (by simp)]
        have hD := divHalfUp_bounds (rate.val * 1000) 365 (by norm_num)
        have hD' : -(2 * 10^8 + 365) ≤ divHalfUp (rate.val * 1000) 365 ∧
            divHalfUp (rate.val * 1000) 365 ≤ 2 * 10^8 + 365 := by
          have : |rate.val * 1000| ≤ 10^8 := abs_le.2 ⟨by omega, by omega⟩
          omega
        have hdays : (0:Int) ≤ (days.val : Int) ∧ (days.val : Int) ≤ 65535 := by
          have := days.hBounds; simp at this; omega
        obtain ⟨p1, p2, p3, p4⟩ := prod_bound bal.val _ _ hb hD' hdays
        have c2 : -170141183460469231731687303715884105728 ≤ bal.val * divHalfUp (rate.val * 1000) 365 ∧
            bal.val * divHalfUp (rate.val * 1000) 365 ≤ 170141183460469231731687303715884105727 := by
          omega
        have c3 : -170141183460469231731687303715884105728 ≤
              bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int) ∧
            bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int) ≤
              170141183460469231731687303715884105727 := by
          omega
        aeneas_wp [core.num.I128.abs, c2, c3]
        rw [wp_div_half_up _ _ _ (by simp) (by simp; omega) (by simp)]
        have hI := divHalfUp_bounds (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int))
          100000000 (by norm_num)
        have habs : |bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)| ≤ 2 ^ 120 :=
          abs_le.2 ⟨p1, p2⟩
        have c4 : -170141183460469231731687303715884105728 ≤
              -divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000 ∧
            -divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000 ≤
              170141183460469231731687303715884105727 := by omega
        have c5 : -170141183460469231731687303715884105728 ≤
              bal.val + divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000 ∧
            bal.val + divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000 ≤
              170141183460469231731687303715884105727 := by omega
        have c6 : -170141183460469231731687303715884105728 ≤
              -(bal.val + divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000) ∧
            -(bal.val + divHalfUp (bal.val * divHalfUp (rate.val * 1000) 365 * (days.val : Int)) 100000000) ≤
              170141183460469231731687303715884105727 := by omega
        aeneas_wp [core.num.I128.abs, c4, c5, c6]
        split_ifs <;>
        · refine ⟨_, _, _, rfl, ?_⟩
          simp (disch := omega) only [cast_I64_ofIntCore, IScalar.ofInt_val_eq]
          rw [accrueModel, ite_eq_right (by simp [h0])]
          simp only [absI]
          split_ifs <;> simp_all
    · rw [not_or] at hT
      have h1 : (t != 'S') = true := by simpa using hT.1
      have h2 : (t != 'C') = true := by simpa using hT.2
      simp only [lift, bind_ok, h0', ite_false, h1, h2, ite_true, Bool.false_eq_true]
      simp [accrueModel, hT]

theorem unwrap_or_val (b : Option I64) :
    (core.option.Option.unwrap_or b 0#i64).val = (b.map (·.val)).getD 0 := by
  cases b <;> simp [core.option.Option.unwrap_or]

/-- The same as an equivalence with the pure model (`pureVal`). -/
theorem accrue_equiv_model (t : Char) (b : Option I64) (rate : I64) (days : U16)
    (hb : -10^13 ≤ (b.map (·.val)).getD 0 ∧ (b.map (·.val)).getD 0 ≤ 10^13)
    (hr : -10^5 ≤ rate.val ∧ rate.val ≤ 10^5) :
    Equiv (fun o r => ∃ x y c, o = .ok (x, y, c) ∧ (x.val, y.val, c) = r)
      (acctint.accrue t b rate days)
      (pureVal (accrueModel t ((b.map (·.val)).getD 0) rate.val days.val)) := by
  rw [equiv_pureVal_iff]
  have h := accrue_spec t b rate days (by rw [unwrap_or_val]; exact hb) hr
  rw [unwrap_or_val] at h
  exact h

end EquivLean.Demo.Aeneas.AcctInt

#print axioms EquivLean.Demo.Aeneas.AcctInt.accrue_equiv_model
