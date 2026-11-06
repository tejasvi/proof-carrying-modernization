import EquivLean.Modernize.Cbact01c.JavaRunHelpers

/-!
# CBACT01C → Java: closers for the goals `jverify` leaves in `zoned`

The step of the `div` loop (`10 ^ i` stays below `2 ^ 64` and `10 ^ 18`), the step of `div` in
the digit loop, and the last digit (`i = n - 1`, the branch substitutes `n - 1` for `i`).
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

theorem zl_pow {k : Nat} (h : k ≤ 17) : 10 ^ k < 18446744073709551616 :=
  Nat.lt_of_lt_of_le (pow10_lt18 h) (by decide)

theorem zl_pow_mod {k : Nat} (h : k ≤ 17) :
    10 ^ k % 18446744073709551616 < 1000000000000000000 := by
  rw [Nat.mod_eq_of_lt (zl_pow h)]; exact pow10_lt18 h

theorem natAbs_toInt_of_nonneg (x : BitVec 64) (h : 0 ≤ x.toInt) : x.toInt.natAbs = x.toNat := by
  rw [toNat_of_toInt_nonneg x h]; omega

theorem i32_sub_one_toInt (n : I32) (h : 1 ≤ n.toInt) : (n - 1#32).toInt = n.toInt - 1 := by
  rw [BitVec.toInt_sub]
  have := n.toInt_lt; have := n.le_toInt
  have h1 : (1#32 : BitVec 32).toInt = 1 := by decide
  rw [h1]
  simp only [Nat.reducePow] at *
  rw [Int.bmod_def]; split <;> omega

/-- `div` after the step of the digit loop. -/
theorem zl_div {n i : I32} {d : I64} (hd0 : 0 ≤ d.toInt) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt + 1 < n.toInt)
    (hd : i.toInt < n.toInt → d.toNat = 10 ^ (n.toInt.toNat - 1 - i.toInt.toNat)) :
    d.toInt.natAbs / 10 = 10 ^ (n.toInt.toNat - 1 - (i.toInt.toNat + 1)) := by
  rw [natAbs_toInt_of_nonneg d hd0, hd (by omega), pow10_div10 (by omega)]
  congr 1 <;> omega

theorem zonedPre_last {A N : Nat} {s ng : Bool} (h : 1 ≤ N) :
    zonedPre A N s ng N = zonedPre A N s ng (N - 1) ++ [zch A N s ng (N - 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]; rfl

/-- The facts at the last digit: `div = 1`, `a = |v|`. -/
theorem zl_last_facts {A : Nat} {n : I32} {a d : I64} (hn1 : 1 ≤ n.toInt) (ha : a.toNat = A)
    (ha0 : 0 ≤ a.toInt) (hd0 : 0 ≤ d.toInt)
    (hd : (n - 1#32).toInt < n.toInt → d.toNat = 10 ^ (n.toInt.toNat - 1 - (n - 1#32).toInt.toNat)) :
    a.toInt.natAbs / d.toInt.natAbs = A := by
  have h1 := i32_sub_one_toInt n hn1
  have h2 : n.toInt.toNat - 1 - (n - 1#32).toInt.toNat = 0 := by rw [h1]; omega
  rw [natAbs_toInt_of_nonneg a ha0, natAbs_toInt_of_nonneg d hd0, hd (by omega), h2, ha]
  simp

/-- The last digit, unsigned (or not `signed`). -/
theorem zl_plain {A : Nat} {ng : Bool} {n : I32} {a d : I64}
    (hn1 : 1 ≤ n.toInt) (ha : a.toNat = A) (ha0 : 0 ≤ a.toInt) (hd0 : 0 ≤ d.toInt)
    (hd : (n - 1#32).toInt < n.toInt → d.toNat = 10 ^ (n.toInt.toNat - 1 - (n - 1#32).toInt.toNat)) :
    zonedPre A n.toInt.toNat false ng (n.toInt.toNat - 1) ++
      [BitVec.ofNat 16 (48 + a.toInt.natAbs / d.toInt.natAbs % 10)] =
    zonedPre A n.toInt.toNat false ng n.toInt.toNat := by
  rw [zonedPre_last (N := n.toInt.toNat) (by omega), zl_last_facts hn1 ha ha0 hd0 hd]
  simp only [zch, Bool.false_eq_true, false_and, ↓reduceIte, digitJ]
  have : n.toInt.toNat - 1 - (n.toInt.toNat - 1) = 0 := by omega
  rw [this]; simp

/-- The last digit, `signed`: the overpunched character `c`. -/
theorem zl_signed {A : Nat} {ng : Bool} {n : I32} {a d : I64} {c : JChar}
    (hd : (n - 1#32).toInt < n.toInt → d.toNat = 10 ^ (n.toInt.toNat - 1 - (n - 1#32).toInt.toNat))
    (ha : a.toNat = A) (hn1 : 1 ≤ n.toInt) (ha0 : 0 ≤ a.toInt) (hd0 : 0 ≤ d.toInt)
    (hc : c = BitVec.ofNat 16 (overpunch ng (a.toInt.natAbs / d.toInt.natAbs % 10))) :
    zonedPre A n.toInt.toNat true ng (n.toInt.toNat - 1) ++ [c] =
    zonedPre A n.toInt.toNat true ng n.toInt.toNat := by
  rw [zonedPre_last (N := n.toInt.toNat) (by omega), hc, zl_last_facts hn1 ha ha0 hd0 hd]
  have : n.toInt.toNat - 1 + 1 = n.toInt.toNat := by omega
  simp only [zch, true_and, this, ↓reduceIte]

/-- The overpunched character of the Java code, from the branch facts in the context. -/
macro "zoned_hc" : tactic => `(tactic| (
  simp only [overpunch, Bool.false_eq_true, ↓reduceIte]
  split <;> first | rfl | (exfalso; contradiction)))

/-- The closer for the leftovers of `zoned_vc`. -/
macro "zoned_close" : tactic => `(tactic| first
  | exact zl_pow (by omega)
  | exact zl_pow_mod (by omega)
  | (apply zl_div <;> assumption)
  | (apply zl_plain <;> assumption)
  | (apply zl_signed <;> first | assumption | zoned_hc))

end EquivLean.Modernize.Cbact01c.Java
