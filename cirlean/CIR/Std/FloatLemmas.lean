import CIR.Std.Float

/-!
  Facts about `printf`'s floating-point conversions for symbolic doubles
  (`CIR/Std/Float.lean`): every double except NaN converts, and the text is
  short and made of printable characters. With precision `P`, `%g` prints
  at most `P + 7` characters (sign, `P` digits, point, `e±ddd`): 24 for
  `%1.17g`, so cJSON's `number_buffer[26]` holds it with its terminator.
-/

namespace CIR.Std

theorem sciDigits_length (P m : Nat) (e : Int) : (sciDigits P m e).1.length = P := by
  unfold sciDigits
  dsimp only
  split
  · simp
  · split <;> simp

theorem sciDigits_lt_ten {P m : Nat} {e : Int} {d : Nat} (h : d ∈ (sciDigits P m e).1) : d < 10 := by
  unfold sciDigits at h
  dsimp only at h
  split at h
  · simp at h; omega
  · split at h <;> (simp at h; obtain ⟨_, _, rfl⟩ := h; exact Nat.mod_lt _ (by decide))

theorem sciDigits_exp (P m : Nat) (e : Int) :
    -999 ≤ (sciDigits P m e).2 ∧ (sciDigits P m e).2 ≤ 999 := by
  unfold sciDigits
  dsimp only
  split
  · simp
  · split <;> simp <;> omega

theorem expChars_length (u : Bool) {X : Int} (h0 : -999 ≤ X) (h1 : X ≤ 999) :
    (expChars u X).length ≤ 5 := by
  have : X.natAbs < 1000 := by omega
  simp only [expChars, List.length_cons]
  split
  · simp
  · split
    · simp
    · simp

theorem stripZeros_length_le (ds : List Nat) : (stripZeros ds).length ≤ ds.length := by
  unfold stripZeros
  simp only [List.length_reverse]
  exact Nat.le_trans (List.dropWhile_sublist _).length_le (by simp)

theorem digitChars_length (ds : List Nat) : (digitChars ds).length = ds.length := by
  simp [digitChars]

/-- `%g` with precision `prec` prints at most `P + 6` characters after the
sign (`P` the precision, at least 1). -/
theorem fmtG_length (alt upper : Bool) (prec m : Nat) (e : Int) :
    (fmtG alt upper prec m e).length ≤ (if prec = 0 then 1 else prec) + 6 := by
  unfold fmtG
  dsimp only
  generalize hP : (if prec = 0 then 1 else prec) = P
  have hP1 : 1 ≤ P := by subst hP; split <;> omega
  have hl := sciDigits_length P m e
  have hx := sciDigits_exp P m e
  have he := expChars_length upper hx.1 hx.2
  generalize sciDigits P m e = r at hl hx he ⊢
  obtain ⟨ds, X⟩ := r
  dsimp only at hl hx he ⊢
  have hs1 := stripZeros_length_le (ds.drop (X.toNat + 1))
  have hs2 := stripZeros_length_le (List.replicate ((-X).toNat - 1) 0 ++ ds)
  have hs3 := stripZeros_length_le (ds.drop 1)
  split
  · simp only [List.length_append, digitChars_length, List.length_take, List.length_cons] at *
    omega
  · split
    · split
      all_goals (split <;> split <;> simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_take, List.length_drop, List.length_replicate,
        digitChars_length] at * <;> omega)
    · split <;> split <;> simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_take, List.length_drop, List.length_replicate,
        digitChars_length] at * <;> omega

/-- `%e` with precision `prec` prints at most `prec + 7` characters after the sign. -/
theorem fmtE_length (alt upper : Bool) (prec m : Nat) (e : Int) :
    (fmtE alt upper prec m e).length ≤ prec + 7 := by
  unfold fmtE
  dsimp only
  have hl := sciDigits_length (prec + 1) m e
  have hx := sciDigits_exp (prec + 1) m e
  have he := expChars_length upper hx.1 hx.2
  generalize sciDigits (prec + 1) m e = r at hl hx he ⊢
  obtain ⟨ds, X⟩ := r
  dsimp only at hl hx he ⊢
  simp only [List.length_append, digitChars_length, List.length_take]
  split <;> simp only [List.length_cons, List.length_nil, digitChars_length, List.length_drop] <;> omega

theorem sign_length (neg plus space : Bool) :
    (if neg = true then [(45 : Int)] else if plus = true then [43] else if space = true then [32] else []).length ≤ 1 := by
  split
  · simp
  · split
    · simp
    · split <;> simp

/-- A conversion `%e`, `%E`, `%g`, `%G` of a double that is not NaN gives a
sign of at most one character and a body of at most `P + 6` characters
(`P` the precision, at least 1, 6 by default; `prec + 1` for `%e`). -/
theorem fmtFloat_eg {c : Int} {alt plus space : Bool} {prec : Option Nat} {x : Float}
    (hc : c = 101 ∨ c = 69 ∨ c = 103 ∨ c = 71) (hx : decodeF x ≠ .nan) :
    ∃ s b, fmtFloat c alt plus space prec x = some (s, b) ∧ s.length ≤ 1 ∧
      b.length ≤ (if c = 101 ∨ c = 69 then prec.getD 6 + 1 else max (prec.getD 6) 1) + 6 := by
  unfold fmtFloat
  dsimp only
  split
  · rename_i h; exact absurd h hx
  · refine ⟨_, _, rfl, sign_length .., ?_⟩
    split <;> simp <;> omega
  · rename_i neg mm ee _
    refine ⟨_, _, rfl, sign_length .., ?_⟩
    rcases hc with rfl | rfl | rfl | rfl
    · simpa using fmtE_length alt false (prec.getD 6) mm ee
    · simpa using fmtE_length alt true (prec.getD 6) mm ee
    · have := fmtG_length alt false (prec.getD 6) mm ee
      simp only [Int.reduceEq, or_self, ite_false, Int.reduceBEq, Bool.or_false,
        Bool.false_eq_true] at *
      split at this <;> omega
    · have := fmtG_length alt true (prec.getD 6) mm ee
      simp only [Int.reduceEq, or_self, ite_false, Int.reduceBEq, Bool.or_false,
        Bool.false_eq_true, Bool.or_true] at *
      split at this <;> omega

end CIR.Std
