import EquivLean.Demo.XLang.TinyRegex.CClass
import EquivLean.Demo.XLang.TinyRegex.CMeta

/-!
# tiny-regex-c → model, C side: `matchcharclass`

`matchcharclass(c, str)` walks the class string at `str` = `&ccl_buf[k]` (block `bc` holding
`xs.map .int`) up to its NUL at index `e`: a range, an escape (`\d`, ..., or an escaped
character), or the character itself (`-` only first or last).  `cclC xs c k` is the C
algorithm on the bytes; the loop invariant is that the positions passed did not match.
-/

open CIR CIR.Std EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- `matchcharclass(c, &xs[j])`, the C algorithm on the class bytes. -/
def cclC (xs : List Int) (c : Int) (j : Nat) : Bool :=
  if rangeP c xs j then true
  else if xs.getD j 0 = 92 then
    if metaP c (xs.getD (j + 1) 0) then true
    else if c = s8 (xs.getD (j + 1) 0) ∧ ¬ metacharP c then true
    else if _h : j + 1 < xs.length ∧ xs.getD (j + 1) 0 ≠ 0 then cclC xs c (j + 2) else false
  else if c = s8 (xs.getD j 0) then
    if c = 45 then decide (xs.getD (j - 1) 0 = 0) || decide (xs.getD (j + 1) 0 = 0) else true
  else if _h : j < xs.length ∧ xs.getD j 0 ≠ 0 then cclC xs c (j + 1) else false
termination_by xs.length - j

/-! ### One step of `cclC` -/

theorem cclC_range {xs : List Int} {c : Int} {j : Nat} (h : rangeP c xs j) : cclC xs c j = true := by
  rw [cclC, ite_eq_left h]

theorem cclC_meta {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 = 92)
    (h2 : metaP c (xs.getD (j + 1) 0)) : cclC xs c j = true := by
  rw [cclC, ite_eq_right h0, ite_eq_left h1, ite_eq_left h2]

theorem cclC_esc {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 = 92)
    (h2 : ¬ metaP c (xs.getD (j + 1) 0)) (h3 : c = s8 (xs.getD (j + 1) 0)) (h4 : ¬ metacharP c) :
    cclC xs c j = true := by
  rw [cclC, ite_eq_right h0, ite_eq_left h1, ite_eq_right h2, ite_eq_left ⟨h3, h4⟩]

theorem cclC_esc_next {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 = 92)
    (h2 : ¬ metaP c (xs.getD (j + 1) 0)) (h3 : ¬ (c = s8 (xs.getD (j + 1) 0) ∧ ¬ metacharP c))
    (h4 : j + 1 < xs.length) (h5 : xs.getD (j + 1) 0 ≠ 0) : cclC xs c j = cclC xs c (j + 2) := by
  rw [cclC, ite_eq_right h0, ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, dite_eq_left ⟨h4, h5⟩]

theorem cclC_esc_end {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 = 92)
    (h2 : ¬ metaP c (xs.getD (j + 1) 0)) (h3 : ¬ (c = s8 (xs.getD (j + 1) 0) ∧ ¬ metacharP c))
    (h5 : xs.getD (j + 1) 0 = 0) : cclC xs c j = false := by
  rw [cclC, ite_eq_right h0, ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, dite_eq_right (fun h => h.2 h5)]

theorem cclC_char {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 ≠ 92)
    (h2 : c = s8 (xs.getD j 0)) (h3 : c ≠ 45) : cclC xs c j = true := by
  rw [cclC, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]

theorem cclC_dash {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 ≠ 92)
    (h2 : c = s8 (xs.getD j 0)) (h3 : c = 45) :
    cclC xs c j = (decide (xs.getD (j - 1) 0 = 0) || decide (xs.getD (j + 1) 0 = 0)) := by
  rw [cclC, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, ite_eq_left h3]

theorem cclC_next {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 ≠ 92)
    (h2 : c ≠ s8 (xs.getD j 0)) (h4 : j < xs.length) (h5 : xs.getD j 0 ≠ 0) :
    cclC xs c j = cclC xs c (j + 1) := by
  rw [cclC, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, dite_eq_left ⟨h4, h5⟩]

theorem cclC_end {xs : List Int} {c : Int} {j : Nat} (h0 : ¬ rangeP c xs j) (h1 : xs.getD j 0 ≠ 92)
    (h2 : c ≠ s8 (xs.getD j 0)) (h5 : xs.getD j 0 = 0) : cclC xs c j = false := by
  rw [cclC, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, dite_eq_right (fun h => h.2 h5)]

/-! ### The contract -/

theorem lt_of_getD_ne {xs : List Int} {e i : Nat} (he0 : xs.getD e 0 = 0) (hie : i ≤ e)
    (h : xs.getD i 0 ≠ 0) : i < e := by
  rcases Nat.lt_or_ge i e with h' | h'
  · exact h'
  · exfalso
    have hse : i = e := by omega
    rw [hse] at h
    exact h he0

end EquivLean.Demo.XLang.TinyRegex.C
