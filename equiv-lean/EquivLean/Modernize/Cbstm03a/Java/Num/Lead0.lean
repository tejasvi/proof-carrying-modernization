import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-! # `fmtZ`'s count of leading zeros -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (digitChar)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem lead0_cons (c : JChar) (s : JStr) : lead0 (c :: s) = if c = digitChar 0 then lead0 s + 1 else 0 := rfl

theorem lead0_le_length : ∀ s : JStr, lead0 s ≤ s.length
  | [] => Nat.le_refl _
  | c :: s => by
    have := lead0_le_length s
    rw [lead0_cons, List.length_cons]
    split <;> omega

theorem lead0_step : ∀ (s : JStr) (k : Nat), k ≤ lead0 s → (h : k < s.length) → s[k] = digitChar 0 →
    k + 1 ≤ lead0 s
  | [], _, _, h, _ => absurd h (by simp)
  | c :: s, 0, _, _, hc => by
    simp only [List.getElem_cons_zero] at hc
    rw [lead0_cons, if_pos hc]
    omega
  | c :: s, k + 1, hk, h, hc => by
    rw [lead0_cons] at hk ⊢
    by_cases h0 : c = digitChar 0
    · rw [if_pos h0] at hk ⊢
      have h' : k < s.length := by simp only [List.length_cons] at h; omega
      have hc' : s[k] = digitChar 0 := by simpa using hc
      have := lead0_step s k (by omega) h' hc'
      omega
    · rw [if_neg h0] at hk
      omega

theorem lead0_stop : ∀ (s : JStr) (k : Nat), k ≤ lead0 s → (h : k < s.length) → ¬ s[k] = digitChar 0 →
    lead0 s = k
  | [], _, _, h, _ => absurd h (by simp)
  | c :: s, 0, _, _, hc => by
    simp only [List.getElem_cons_zero] at hc
    rw [lead0_cons, if_neg hc]
  | c :: s, k + 1, hk, h, hc => by
    rw [lead0_cons] at hk ⊢
    by_cases h0 : c = digitChar 0
    · rw [if_pos h0] at hk ⊢
      have h' : k < s.length := by simp only [List.length_cons] at h; omega
      have hc' : ¬ s[k] = digitChar 0 := by simpa using hc
      have := lead0_stop s k (by omega) h' hc'
      omega
    · rw [if_neg h0] at hk
      omega

theorem lead0_full (s : JStr) (k : Nat) (hk : k ≤ lead0 s) (hl : s.length ≤ k) : lead0 s = k := by
  have := lead0_le_length s
  omega

/-- `(int) c == '0'`. -/
theorem char48_iff (c : JChar) : BitVec.setWidth 32 c = 48#32 ↔ c = digitChar 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    have hc := c.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, digitChar] at this ⊢
    omega
  · rintro rfl
    rfl

end EquivLean.Modernize.Cbstm03a.Java
