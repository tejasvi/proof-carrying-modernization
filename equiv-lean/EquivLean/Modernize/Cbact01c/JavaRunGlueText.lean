import EquivLean.Modernize.Cbact01c.JavaRunText

/-!
# CBACT01C → Java: the helpers' texts in closed form

`fixStr s n = s` for a text of the field's length; `zonedJ` is the DISPLAY text of a numeric
field (`fieldTextS`): the digits zero-padded, the last one overpunched with the sign when signed.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

theorem fixStr_eq_map (s : JStr) : ∀ n, fixStr s n = (List.range n).map (fun i => s.getD i space)
  | 0 => rfl
  | n + 1 => by rw [fixStr, fixStr_eq_map s n, List.range_succ, List.map_append]; rfl

/-- A text of the field's length is displayed as it is. -/
theorem fixStr_eq_self {s : JStr} {n : Nat} (h : s.length = n) : fixStr s n = s := by
  subst h
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [h2]

theorem fixStr_length (s : JStr) (n : Nat) : (fixStr s n).length = n := by
  rw [fixStr_eq_map]; simp

/-- `n` spaces. -/
theorem fixStr_nil (n : Nat) : fixStr [] n = List.replicate n space := by
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The first `k ≤ n` characters of `pad(s, n)` are those of `pad(s, k)`. -/
theorem fixStr_take (s : JStr) {k n : Nat} (h : k ≤ n) : (fixStr s n).take k = fixStr s k := by
  rw [fixStr_eq_map, fixStr_eq_map, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## `zoned` -/

theorem zonedPre_length (A n : Nat) (s ng : Bool) : ∀ i, (zonedPre A n s ng i).length = i
  | 0 => rfl
  | i + 1 => by simp [zonedPre, zonedPre_length A n s ng i]

/-- Before the last position the sign plays no part. -/
theorem zonedPre_signed (A n : Nat) (ng : Bool) : ∀ i, i < n →
    zonedPre A n true ng i = zonedPre A n false ng i
  | 0, _ => rfl
  | i + 1, h => by
    rw [zonedPre, zonedPre, zonedPre_signed A n ng i (by omega)]
    congr 2
    simp only [zch, true_and, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [if_neg (by omega)]

/-- One digit more on the left: the digits of `A / 10` in one place less. -/
theorem zonedPre_shift (A n : Nat) (ng : Bool) : ∀ i, i ≤ n →
    zonedPre A (n + 1) false ng i = zonedPre (A / 10) n false ng i
  | 0, _ => rfl
  | i + 1, h => by
    rw [zonedPre, zonedPre, zonedPre_shift A n ng i (by omega)]
    congr 2
    simp only [zch, Bool.false_eq_true, false_and, ↓reduceIte, digitJ]
    have h1 : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
    rw [h1, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-- The unsigned text: the zero-padded digits. -/
theorem zonedPre_unsigned (ng : Bool) : ∀ n A,
    zonedPre A n false ng n = ((Cobol.Digits.toDigits 10 n A).map (48 + ·)).map (BitVec.ofNat 16)
  | 0, _ => rfl
  | n + 1, A => by
    rw [zonedPre, zonedPre_shift A n ng n (Nat.le_refl _), zonedPre_unsigned ng n (A / 10)]
    simp only [Cobol.Digits.toDigits, List.map_append, List.map_cons, List.map_nil, zch, Bool.false_eq_true,
      false_and, ↓reduceIte, digitJ, Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]

theorem jline_append (a b : List Nat) : jline (a ++ b) = jline a ++ jline b := by
  simp [jline]

/-- `zoned(v, n, false)` is the text of an unsigned DISPLAY field of `n` digits. -/
theorem zonedJ_unsigned (v : Int) (n : Nat) : zonedJ v n false = jline (zpad n v.natAbs) := by
  rw [zonedJ, zonedPre_unsigned]; rfl

/-- `zoned(v, n, true)` is the text of a signed DISPLAY field of `n` digits (trailing embedded
sign). -/
theorem zonedJ_signed (v : Int) (n : Nat) (h : 1 ≤ n) :
    zonedJ v n true =
      jline (zpad (n - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)]) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [zonedJ, zonedPre, zonedPre_signed _ _ _ m (by omega), zonedPre_shift _ m _ m (Nat.le_refl _),
    zonedPre_unsigned, jline_append, Nat.add_sub_cancel]
  simp only [zch, true_and, ↓reduceIte, jline, zpad, List.map_cons, List.map_nil]

end EquivLean.Modernize.Cbact01c.Java
