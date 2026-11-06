import EquivLean.Modernize.Cbstm03a.Java.Text.Fin

/-!
# CBSTM03A → Java: `Iface3`'s texts of `fmtZ` and `star` as `Iface1`'s

`fmtZI_eq : fmtZI v = fmtZStr v`, `starT_eq : starT p f = starStr p f` (and `appT` as `appStr`), with the lengths
of the texts.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space fixStr_length zpadStr_length
  digitChar)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

theorem lead0T_eq (s : JStr) : lead0T s = lead0 s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    unfold lead0T at ih ⊢
    unfold List.takeWhile lead0
    by_cases h : c = digitChar 0
    · rw [if_pos h]
      have h' : (c == chZero) = true := by rw [h]; rfl
      rw [h']
      simp only [List.length_cons, ih]
    · rw [if_neg h]
      have h' : (c == chZero) = false := by
        rw [beq_eq_false_iff_ne]; intro e; exact h (by rw [e]; rfl)
      rw [h']
      rfl

theorem zpadStr_modN : ∀ (m c : Nat), zpadStr (c % 10 ^ m) m = zpadStr c m
  | 0, _ => rfl
  | m + 1, c => by
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 := by
      rw [Nat.pow_succ']; exact Nat.mod_mul_right_mod c 10 (10 ^ m)
    simp only [zpadStr, h1, h2, zpadStr_modN m (c / 10)]

theorem dot_lit : JStr.ofString "." = [chDot] := by decide
theorem dash_lit : JStr.ofString "-" = [chDash] := by decide
theorem space_lit : JStr.ofString " " = [space] := by decide
theorem star_lit : JStr.ofString "*" = [chStar] := by decide

theorem fmtZI_eq (v : Int) : fmtZI v = fmtZStr v := by
  have hA : v.natAbs % 100000000000 / 100 = v.natAbs / 100 % 10 ^ 9 := by
    rw [show (100000000000 : Nat) = 100 * 10 ^ 9 from rfl, Nat.mod_mul_right_div_self]
  have hB : v.natAbs % 100000000000 % 100 = v.natAbs % 10 ^ 2 := by
    rw [show (100000000000 : Nat) = 100 * 10 ^ 9 from rfl, Nat.mod_mul_right_mod]; rfl
  simp only [fmtZI, fmtZStr, hA, hB, zpadStr_modN, lead0T_eq, signStr, dot_lit]
  by_cases h : v < 0
  · simp only [h, if_true, dash_lit]
  · simp only [h, if_false, space_lit]

theorem appT_eq (dst : JStr) (cap : Nat) (src : JStr) (d : Option JStr) :
    appT dst cap src d = appStr dst (cap : Int) src d := by
  have hc : ∀ d, appT dst cap src d = dst ++ (cutAt src d).take (cap - dst.length) := by
    intro d; cases d <;> rfl
  rw [hc]
  unfold appStr
  by_cases h : (cap : Int) - (dst.length : Int) ≤ 0
  · rw [if_pos h]
    have h0 : cap - dst.length = 0 := by omega
    rw [h0, List.take_zero, List.append_nil]
  · rw [if_neg h]
    have h0 : ((cap : Int) - (dst.length : Int)).toNat = cap - dst.length := by omega
    rw [h0]

theorem starT_eq (p f : JStr) : starT p f = starStr p f := by
  simp only [starT, starStr, appT_eq, jl, star_lit]
  rfl

theorem takeWhile_length_le {α : Type} (p : α → Bool) : ∀ (l : List α), (l.takeWhile p).length ≤ l.length
  | [] => by simp
  | a :: l => by
    unfold List.takeWhile
    split <;> simp [takeWhile_length_le p l] <;> omega

@[simp] theorem fmtZStr_length (v : Int) : (fmtZStr v).length = 13 := by
  rw [← fmtZI_eq]
  have h : lead0T (zpadStr (v.natAbs % 100000000000 / 100) 9) ≤ 9 := by
    have := takeWhile_length_le (· == chZero) (zpadStr (v.natAbs % 100000000000 / 100) 9)
    rw [zpadStr_length] at this
    exact this
  simp only [fmtZI, List.length_append, List.length_replicate, List.length_drop, zpadStr_length, List.length_cons,
    List.length_nil]
  omega

@[simp] theorem starStr_length (p f : JStr) : (starStr p f).length = 100 := fixStr_length _ _

@[simp] theorem paraStr_length (p f : JStr) : (paraStr p f).length = 100 := fixStr_length _ _

end EquivLean.Modernize.Cbstm03a.Java.Txt
