/-!
# Integer facts for C arithmetic idioms

Range facts that `omega` cannot derive (division by a variable). Certificates import this file, and
patch proposals may use its lemmas in proof scripts.
-/

namespace VerifOrch

/-- `a / b` of two `int`s stays in range unless `b = 0` or `INT_MIN / -1`. -/
theorem tdiv_in_i32 (a b : Int) (ha : -2147483648 ≤ a ∧ a ≤ 2147483647) (hb0 : b ≠ 0)
    (hov : ¬ (a = -2147483648 ∧ b = -1)) :
    -2147483648 ≤ a.tdiv b ∧ a.tdiv b ≤ 2147483647 := by
  have hle := Int.natAbs_tdiv_le_natAbs a b
  by_cases hm : a = -2147483648
  · subst hm
    by_cases h1 : b = 1
    · subst h1; simp
    · have hb : b ≠ -1 := fun h => hov ⟨rfl, h⟩
      have h2 : 2 ≤ b.natAbs := by omega
      have hq : (Int.tdiv (-2147483648) b).natAbs = 2147483648 / b.natAbs := by
        rw [Int.natAbs_tdiv]; rfl
      have h3 : 2147483648 / b.natAbs ≤ 2147483648 / 2 := Nat.div_le_div_left h2 (by decide)
      omega
  · omega

end VerifOrch
