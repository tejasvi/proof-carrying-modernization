import EquivLean.Demo.XLang.Jsmn.Model

/-!
# jsmn model: facts for the C and Rust sides

* Positions: `primScan_ge`, `primScan_le`, `strScan_ge`, `strScan_lt`, `parsePrimitive_pos`,
  `parseString_pos`, and `step_pos_lt`: every turn of the loop moves `pos` forward, so the test in
  `mainLoop` always holds and `mainLoop_eq` unfolds the loop without it.
* The backward searches stay below their start: `lastOpen_lt`, `lastOpenCont_lt`.
* The invariant `Inv` (`step_inv`, `mainLoop_inv`): `toksuper` is -1 or a token's index, at most
  `num_tokens` tokens and at most one per byte read, `pos` within the text, and every token within
  bounds (`TokOk`: a known type, `start` and `end` within the bytes read, `size` at most the
  number of tokens).  These are the ranges the C and Rust sides need for their indices and `int`
  arithmetic.
* Error codes: `step_err`, `mainLoop_err`; and `parse_cases`, what `parse` returns.
-/

namespace EquivLean.Demo.XLang.Jsmn

theorem primScan_ge (js : List Nat) (p : Nat) {e : Nat} (h : primScan js p = some e) : p ≤ e := by
  rw [primScan] at h
  by_cases hl : live js p
  · rw [dite_eq_left hl] at h
    dsimp only at h
    by_cases hd : primDelim (byteAt js p) = true
    · rw [ite_eq_left hd] at h; cases h; exact Nat.le_refl _
    · rw [ite_eq_right hd] at h
      by_cases hc : byteAt js p < 32 ∨ 127 ≤ byteAt js p
      · rw [ite_eq_left hc] at h; cases h
      · rw [ite_eq_right hc] at h
        have := primScan_ge js (p + 1) h
        omega
  · rw [dite_eq_right hl] at h; cases h; exact Nat.le_refl _
termination_by js.length - p
decreasing_by have := hl.1; omega

theorem primScan_le (js : List Nat) (p : Nat) {e : Nat} (hp : p ≤ js.length)
    (h : primScan js p = some e) : e ≤ js.length := by
  rw [primScan] at h
  by_cases hl : live js p
  · rw [dite_eq_left hl] at h
    dsimp only at h
    by_cases hd : primDelim (byteAt js p) = true
    · rw [ite_eq_left hd] at h; cases h; exact hp
    · rw [ite_eq_right hd] at h
      by_cases hc : byteAt js p < 32 ∨ 127 ≤ byteAt js p
      · rw [ite_eq_left hc] at h; cases h
      · rw [ite_eq_right hc] at h
        exact primScan_le js (p + 1) (by have := hl.1; omega) h
  · rw [dite_eq_right hl] at h; cases h; exact hp
termination_by js.length - p
decreasing_by have := hl.1; omega

theorem strScan_ge (js : List Nat) (p hex : Nat) {q : Nat} (h : strScan js p hex = .ok q) :
    p ≤ q := by
  rw [strScan] at h
  by_cases hl : live js p
  · rw [dite_eq_left hl] at h
    dsimp only at h
    by_cases hh : 0 < hex
    · rw [ite_eq_left hh] at h
      by_cases hx : hexDigit (byteAt js p) = true
      · rw [ite_eq_left hx] at h
        have := strScan_ge js (p + 1) (hex - 1) h
        omega
      · rw [ite_eq_right hx] at h; cases h
    · rw [ite_eq_right hh] at h
      by_cases hq : byteAt js p = 34
      · rw [ite_eq_left hq] at h; cases h; exact Nat.le_refl _
      · rw [ite_eq_right hq] at h
        by_cases hb : byteAt js p = 92 ∧ p + 1 < js.length
        · rw [ite_eq_left hb] at h
          by_cases he : escChar (byteAt js (p + 1)) = true
          · rw [ite_eq_left he] at h
            have := strScan_ge js (p + 2) 0 h
            omega
          · rw [ite_eq_right he] at h
            by_cases hu : byteAt js (p + 1) = 117
            · rw [ite_eq_left hu] at h
              have := strScan_ge js (p + 2) 4 h
              omega
            · rw [ite_eq_right hu] at h; cases h
        · rw [ite_eq_right hb] at h
          have := strScan_ge js (p + 1) 0 h
          omega
  · rw [dite_eq_right hl] at h; cases h
termination_by js.length - p
decreasing_by all_goals (have := hl.1; omega)

theorem strScan_lt (js : List Nat) (p hex : Nat) {q : Nat} (h : strScan js p hex = .ok q) :
    q < js.length := by
  rw [strScan] at h
  by_cases hl : live js p
  · rw [dite_eq_left hl] at h
    dsimp only at h
    by_cases hh : 0 < hex
    · rw [ite_eq_left hh] at h
      by_cases hx : hexDigit (byteAt js p) = true
      · rw [ite_eq_left hx] at h
        exact strScan_lt js (p + 1) (hex - 1) h
      · rw [ite_eq_right hx] at h; cases h
    · rw [ite_eq_right hh] at h
      by_cases hq : byteAt js p = 34
      · rw [ite_eq_left hq] at h; cases h; exact hl.1
      · rw [ite_eq_right hq] at h
        by_cases hb : byteAt js p = 92 ∧ p + 1 < js.length
        · rw [ite_eq_left hb] at h
          by_cases he : escChar (byteAt js (p + 1)) = true
          · rw [ite_eq_left he] at h
            exact strScan_lt js (p + 2) 0 h
          · rw [ite_eq_right he] at h
            by_cases hu : byteAt js (p + 1) = 117
            · rw [ite_eq_left hu] at h
              exact strScan_lt js (p + 2) 4 h
            · rw [ite_eq_right hu] at h; cases h
        · rw [ite_eq_right hb] at h
          exact strScan_lt js (p + 1) 0 h
  · rw [dite_eq_right hl] at h; cases h
termination_by js.length - p
decreasing_by all_goals (have := hl.1; omega)

theorem lastOpen_lt (toks : List Tok) : ∀ i j, lastOpen toks i = some j → j < i
  | 0, j, h => by simp [lastOpen] at h
  | i + 1, j, h => by
    simp only [lastOpen] at h
    split at h
    · cases h; omega
    · have := lastOpen_lt toks i j h; omega

theorem lastOpenCont_lt (toks : List Tok) : ∀ i j, lastOpenCont toks i = some j → j < i
  | 0, j, h => by simp [lastOpenCont] at h
  | i + 1, j, h => by
    simp only [lastOpenCont] at h
    split at h
    · cases h; omega
    · have := lastOpenCont_lt toks i j h; omega

/-- A primitive starting at a live, non-delimiter byte ends after it. -/
theorem primScan_gt {js : List Nat} {p e : Nat} (hl : live js p)
    (hnd : primDelim (byteAt js p) = false) (h : primScan js p = some e) : p < e := by
  rw [primScan, dite_eq_left hl] at h
  dsimp only at h
  rw [ite_eq_right (by rw [hnd]; decide)] at h
  by_cases hc : byteAt js p < 32 ∨ 127 ≤ byteAt js p
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h
    have := primScan_ge js (p + 1) h
    omega

theorem parsePrimitive_pos {js : List Nat} {n : Nat} {st st' : St} (hl : live js st.pos)
    (hnd : primDelim (byteAt js st.pos) = false) (h : parsePrimitive js n st = .ok st') :
    st.pos ≤ st'.pos := by
  unfold parsePrimitive at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · cases h
    · cases h
      have := primScan_gt hl hnd he
      simp only
      omega

theorem parseString_pos {js : List Nat} {n : Nat} {st st' : St}
    (h : parseString js n st = .ok st') : st.pos < st'.pos := by
  unfold parseString at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · cases h
      have := strScan_ge js (st.pos + 1) 0 hq
      simp only
      omega

/-- Every turn of the loop moves `pos` forward. -/
theorem step_pos_lt {js : List Nat} {n : Nat} {st st' : St} (hl : live js st.pos)
    (h : step js n st = .ok st') : st.pos < st'.pos := by
  unfold step at h
  dsimp only at h
  have hnd : ∀ c, c = byteAt js st.pos → ¬ (c = 123 ∨ c = 91) → ¬ (c = 125 ∨ c = 93) →
      ¬ c = 34 → ¬ (c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32) → ¬ c = 58 → ¬ c = 44 →
      primDelim (byteAt js st.pos) = false := by
    intro c hc h1 h2 h3 h4 h5 h6
    subst hc
    simp only [primDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    omega
  generalize hc : byteAt js st.pos = c at h
  by_cases h1 : c = 123 ∨ c = 91
  · rw [ite_eq_left h1] at h
    by_cases hn : n ≤ st.toks.length
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h; cases h; simp
  rw [ite_eq_right h1] at h
  by_cases h2 : c = 125 ∨ c = 93
  · rw [ite_eq_left h2] at h
    split at h
    · cases h
    · rename_i i _
      by_cases ht : (st.toks.getD i dflt).type ≠ (if c = 125 then OBJECT else ARRAY)
      · rw [ite_eq_left ht] at h; cases h
      · rw [ite_eq_right ht] at h; cases h; simp
  rw [ite_eq_right h2] at h
  by_cases h3 : c = 34
  · rw [ite_eq_left h3] at h
    split at h
    · cases h
    · rename_i st'' hps
      cases h
      have := parseString_pos hps
      simp only
      omega
  rw [ite_eq_right h3] at h
  by_cases h4 : c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32
  · rw [ite_eq_left h4] at h; cases h; simp
  rw [ite_eq_right h4] at h
  by_cases h5 : c = 58
  · rw [ite_eq_left h5] at h; cases h; simp
  rw [ite_eq_right h5] at h
  by_cases h6 : c = 44
  · rw [ite_eq_left h6] at h
    split at h <;> (cases h; simp)
  rw [ite_eq_right h6] at h
  split at h
  · cases h
  · rename_i st'' hpp
    cases h
    have := parsePrimitive_pos hl (hnd c hc.symm h1 h2 h3 h4 h5 h6) hpp
    simp only
    omega

/-- `jsmn_parse`'s loop, without the progress test (`step_pos_lt`). -/
theorem mainLoop_eq (js : List Nat) (n : Nat) (st : St) :
    mainLoop js n st =
      if live js st.pos then
        (match step js n st with
         | .error e => .error e
         | .ok st' => mainLoop js n st')
      else .ok st := by
  rw [mainLoop]
  by_cases hl : live js st.pos
  · rw [dite_eq_left hl, ite_eq_left hl]
    cases hs : step js n st with
    | error e => rfl
    | ok st' =>
      dsimp only
      rw [dite_eq_left (step_pos_lt hl hs)]
  · rw [dite_eq_right hl, ite_eq_right hl]

/-! ## The parser invariant -/

/-- The bounds of a token after `jsmn_parse` has read the bytes before `p` and filled `L` tokens:
a known type, `0 ≤ start ≤ p`, `end` is -1 or in `0 .. p`, and `0 ≤ size ≤ L`. -/
def TokOk (p L : Nat) (t : Tok) : Prop :=
  (t.type = OBJECT ∨ t.type = ARRAY ∨ t.type = STRING ∨ t.type = PRIMITIVE) ∧
    0 ≤ t.start ∧ t.start ≤ p ∧ (t.stop = -1 ∨ (0 ≤ t.stop ∧ t.stop ≤ p)) ∧
    0 ≤ t.size ∧ t.size ≤ L

theorem tokOk_mk {p L : Nat} {ty s e z : Int}
    (hty : ty = OBJECT ∨ ty = ARRAY ∨ ty = STRING ∨ ty = PRIMITIVE) (h1 : 0 ≤ s) (h2 : s ≤ p)
    (h3 : e = -1 ∨ (0 ≤ e ∧ e ≤ p)) (h4 : 0 ≤ z) (h5 : z ≤ L) : TokOk p L ⟨ty, s, e, z⟩ :=
  ⟨hty, h1, h2, h3, h4, h5⟩

theorem TokOk.mono {p L p' L' : Nat} {t : Tok} (h : TokOk p L t) (hp : p ≤ p') (hL : L ≤ L') :
    TokOk p' L' t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, by omega, ?_, h5, by omega⟩
  rcases h4 with h4 | h4
  · exact Or.inl h4
  · exact Or.inr ⟨h4.1, by omega⟩

/-- Every token of `xs` is within the bounds `p`, `L`. -/
def AllOk (p L : Nat) (xs : List Tok) : Prop := ∀ k (hk : k < xs.length), TokOk p L xs[k]

theorem AllOk.mono {p L p' L' : Nat} {xs : List Tok} (h : AllOk p L xs) (hp : p ≤ p')
    (hL : L ≤ L') : AllOk p' L' xs := fun k hk => (h k hk).mono hp hL

theorem AllOk.push {p L : Nat} {xs : List Tok} {t : Tok} (h : AllOk p L xs) (ht : TokOk p L t) :
    AllOk p L (xs ++ [t]) := by
  intro k hk
  rw [List.getElem_append]
  split
  · exact h k ‹_›
  · simp only [List.getElem_singleton]; exact ht

theorem AllOk.set {p L : Nat} {xs : List Tok} {i : Nat} {t : Tok} (h : AllOk p L xs)
    (ht : TokOk p L t) : AllOk p L (xs.set i t) := by
  intro k hk
  rw [List.getElem_set]
  split
  · exact ht
  · exact h k (by simpa using hk)

theorem length_bumpSup (toks : List Tok) (sup : Int) : (bumpSup toks sup).length = toks.length := by
  unfold bumpSup incSize; split <;> simp

theorem AllOk.bump {p L : Nat} {xs : List Tok} (sup : Int) (h : AllOk p L xs) :
    AllOk p (L + 1) (bumpSup xs sup) := by
  intro k hk
  have hk' : k < xs.length := by rw [length_bumpSup] at hk; exact hk
  by_cases hs : sup = -1
  · have e : bumpSup xs sup = xs := by simp [bumpSup, hs]
    rw [List.getElem_of_eq e]
    exact (h k hk').mono (Nat.le_refl _) (Nat.le_succ _)
  · have e : bumpSup xs sup = incSize xs sup.toNat := by simp [bumpSup, hs]
    rw [List.getElem_of_eq e]
    simp only [incSize, List.getElem_modify]
    split
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h k hk'
      exact ⟨h1, h2, h3, h4, by dsimp only; omega, by dsimp only; omega⟩
    · exact (h k hk').mono (Nat.le_refl _) (Nat.le_succ _)

theorem getD_of_lt {xs : List Tok} {i : Nat} (h : i < xs.length) : xs.getD i dflt = xs[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The parser invariant along `jsmn_parse`'s loop: `toksuper` is -1 or a token's index; at most
`n` tokens, each taking at least one byte before `pos`; `pos` within the text; every token within
these bounds. -/
structure Inv (js : List Nat) (n : Nat) (st : St) : Prop where
  sup : st.sup = -1 ∨ (0 ≤ st.sup ∧ st.sup < st.toks.length)
  len_n : st.toks.length ≤ n
  len_pos : st.toks.length ≤ st.pos
  pos_le : st.pos ≤ js.length
  toks : AllOk st.pos st.toks.length st.toks

theorem inv_init (js : List Nat) (n : Nat) : Inv js n St.init :=
  ⟨Or.inl rfl, Nat.zero_le _, Nat.le_refl _, Nat.zero_le _,
    fun k hk => absurd hk (by simp [St.init])⟩

theorem parseString_ok {js : List Nat} {n : Nat} {st st' : St}
    (h : parseString js n st = .ok st') :
    ∃ q, strScan js (st.pos + 1) 0 = .ok q ∧ st.toks.length < n ∧
      st' = ⟨q, st.toks ++ [⟨STRING, st.pos + 1, q, 0⟩], st.sup⟩ := by
  unfold parseString at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · cases h
      exact ⟨q, hq, by omega, rfl⟩

theorem parsePrimitive_ok {js : List Nat} {n : Nat} {st st' : St}
    (h : parsePrimitive js n st = .ok st') :
    ∃ e, primScan js st.pos = some e ∧ st.toks.length < n ∧
      st' = ⟨e - 1, st.toks ++ [⟨PRIMITIVE, st.pos, e, 0⟩], st.sup⟩ := by
  unfold parsePrimitive at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · cases h
    · cases h
      exact ⟨e, he, by omega, rfl⟩

/-- Every turn of the loop keeps the invariant. -/
theorem step_inv {js : List Nat} {n : Nat} {st st' : St} (hi : Inv js n st) (hl : live js st.pos)
    (h : step js n st = .ok st') : Inv js n st' := by
  have hpos := hl.1
  obtain ⟨hsup, hlenn, hlenp, hposl, htoks⟩ := hi
  unfold step at h
  dsimp only at h
  have hnd : ∀ c, c = byteAt js st.pos → ¬ (c = 123 ∨ c = 91) → ¬ (c = 125 ∨ c = 93) →
      ¬ c = 34 → ¬ (c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32) → ¬ c = 58 → ¬ c = 44 →
      primDelim (byteAt js st.pos) = false := by
    intro c hc h1 h2 h3 h4 h5 h6
    subst hc
    simp only [primDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    omega
  generalize hc : byteAt js st.pos = c at h
  by_cases h1 : c = 123 ∨ c = 91
  · rw [ite_eq_left h1] at h
    by_cases hn : n ≤ st.toks.length
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h; cases h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [List.length_append, length_bumpSup, List.length_singleton]
      · right; omega
      · omega
      · omega
      · omega
      · refine AllOk.push ((htoks.bump st.sup).mono (by omega) (Nat.le_refl _))
          (tokOk_mk ?_ (by omega) (by omega) (Or.inl rfl) (Int.le_refl 0) (by omega))
        split
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  rw [ite_eq_right h1] at h
  by_cases h2 : c = 125 ∨ c = 93
  · rw [ite_eq_left h2] at h
    split at h
    · cases h
    · rename_i i hi
      have hil : i < st.toks.length := lastOpen_lt _ _ _ hi
      by_cases ht : (st.toks.getD i dflt).type ≠ (if c = 125 then OBJECT else ARRAY)
      · rw [ite_eq_left ht] at h; cases h
      · rw [ite_eq_right ht] at h; cases h
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.length_set]
        · split
          · rename_i j hj
            have := lastOpen_lt _ _ _ hj
            right; omega
          · left; rfl
        · omega
        · omega
        · omega
        · refine AllOk.set (htoks.mono (by omega) (Nat.le_refl _)) ?_
          rw [getD_of_lt hil]
          obtain ⟨t1, t2, t3, -, t5, t6⟩ := htoks i hil
          exact ⟨t1, t2, by dsimp only; omega, Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩,
            t5, t6⟩
  rw [ite_eq_right h2] at h
  by_cases h3 : c = 34
  · rw [ite_eq_left h3] at h
    split at h
    · cases h
    · rename_i st'' hps
      cases h
      obtain ⟨q, hq, hn, rfl⟩ := parseString_ok hps
      have hq1 := strScan_ge js (st.pos + 1) 0 hq
      have hq2 := strScan_lt js (st.pos + 1) 0 hq
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [List.length_append, length_bumpSup, List.length_singleton]
      · rcases hsup with hs | hs
        · exact Or.inl hs
        · right; omega
      · omega
      · omega
      · omega
      · refine AllOk.bump st.sup (AllOk.push (htoks.mono (by omega) (Nat.le_refl _)) ?_)
        exact tokOk_mk (Or.inr (Or.inr (Or.inl rfl))) (by omega) (by omega)
          (Or.inr ⟨by omega, by omega⟩) (Int.le_refl 0) (by omega)
  rw [ite_eq_right h3] at h
  by_cases h4 : c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32
  · rw [ite_eq_left h4] at h; cases h
    exact ⟨hsup, hlenn, by dsimp only; omega, by dsimp only; omega,
      htoks.mono (Nat.le_succ _) (Nat.le_refl _)⟩
  rw [ite_eq_right h4] at h
  by_cases h5 : c = 58
  · rw [ite_eq_left h5] at h; cases h
    exact ⟨by dsimp only; omega, hlenn, by dsimp only; omega, by dsimp only; omega,
      htoks.mono (Nat.le_succ _) (Nat.le_refl _)⟩
  rw [ite_eq_right h5] at h
  by_cases h6 : c = 44
  · rw [ite_eq_left h6] at h
    split at h
    · cases h
      refine ⟨?_, hlenn, by dsimp only; omega, by dsimp only; omega,
        htoks.mono (Nat.le_succ _) (Nat.le_refl _)⟩
      dsimp only
      split
      · rename_i i hi
        have := lastOpenCont_lt _ _ _ hi
        right; omega
      · exact hsup
    · cases h
      exact ⟨hsup, hlenn, by dsimp only; omega, by dsimp only; omega,
        htoks.mono (Nat.le_succ _) (Nat.le_refl _)⟩
  rw [ite_eq_right h6] at h
  split at h
  · cases h
  · rename_i st'' hpp
    cases h
    obtain ⟨e, he, hn, rfl⟩ := parsePrimitive_ok hpp
    have he1 := primScan_gt hl (hnd c hc.symm h1 h2 h3 h4 h5 h6) he
    have he2 := primScan_le js st.pos hposl he
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [List.length_append, length_bumpSup, List.length_singleton]
    · rcases hsup with hs | hs
      · exact Or.inl hs
      · right; omega
    · omega
    · omega
    · omega
    · refine AllOk.bump st.sup (AllOk.push (htoks.mono (by omega) (Nat.le_refl _)) ?_)
      exact tokOk_mk (Or.inr (Or.inr (Or.inr rfl))) (by omega) (by omega)
        (Or.inr ⟨by omega, by omega⟩) (Int.le_refl 0) (by omega)

/-- The loop keeps the invariant. -/
theorem mainLoop_inv {js : List Nat} {n : Nat} (st : St) {st' : St} (hi : Inv js n st)
    (h : mainLoop js n st = .ok st') : Inv js n st' := by
  rw [mainLoop_eq] at h
  by_cases hl : live js st.pos
  · rw [ite_eq_left hl] at h
    cases hs : step js n st with
    | error e => rw [hs] at h; cases h
    | ok st'' =>
      rw [hs] at h
      dsimp only at h
      exact mainLoop_inv st'' (step_inv hi hl hs) h
  · rw [ite_eq_right hl] at h; cases h; exact hi
termination_by js.length - st.pos
decreasing_by have := step_pos_lt hl hs; have := hl.1; omega

/-! ## Error codes -/

theorem strScan_err {js : List Nat} {p hex : Nat} {e : Int} (h : strScan js p hex = .error e) :
    e = ERROR_INVAL ∨ e = ERROR_PART := by
  rw [strScan] at h
  by_cases hl : live js p
  · rw [dite_eq_left hl] at h
    dsimp only at h
    by_cases hh : 0 < hex
    · rw [ite_eq_left hh] at h
      by_cases hx : hexDigit (byteAt js p) = true
      · rw [ite_eq_left hx] at h; exact strScan_err h
      · rw [ite_eq_right hx] at h; cases h; exact Or.inl rfl
    · rw [ite_eq_right hh] at h
      by_cases hq : byteAt js p = 34
      · rw [ite_eq_left hq] at h; cases h
      · rw [ite_eq_right hq] at h
        by_cases hb : byteAt js p = 92 ∧ p + 1 < js.length
        · rw [ite_eq_left hb] at h
          by_cases he : escChar (byteAt js (p + 1)) = true
          · rw [ite_eq_left he] at h; exact strScan_err h
          · rw [ite_eq_right he] at h
            by_cases hu : byteAt js (p + 1) = 117
            · rw [ite_eq_left hu] at h; exact strScan_err h
            · rw [ite_eq_right hu] at h; cases h; exact Or.inl rfl
        · rw [ite_eq_right hb] at h; exact strScan_err h
  · rw [dite_eq_right hl] at h; cases h; exact Or.inr rfl
termination_by js.length - p
decreasing_by all_goals (have := hl.1; omega)

theorem step_err {js : List Nat} {n : Nat} {st : St} {e : Int} (h : step js n st = .error e) :
    e = ERROR_NOMEM ∨ e = ERROR_INVAL ∨ e = ERROR_PART := by
  unfold step at h
  dsimp only at h
  generalize byteAt js st.pos = c at h
  by_cases h1 : c = 123 ∨ c = 91
  · rw [ite_eq_left h1] at h
    by_cases hn : n ≤ st.toks.length
    · rw [ite_eq_left hn] at h; cases h; exact Or.inl rfl
    · rw [ite_eq_right hn] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : c = 125 ∨ c = 93
  · rw [ite_eq_left h2] at h
    split at h
    · cases h; exact Or.inr (Or.inl rfl)
    · rename_i i _
      by_cases ht : (st.toks.getD i dflt).type ≠ (if c = 125 then OBJECT else ARRAY)
      · rw [ite_eq_left ht] at h; cases h; exact Or.inr (Or.inl rfl)
      · rw [ite_eq_right ht] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : c = 34
  · rw [ite_eq_left h3] at h
    split at h
    · rename_i e' hps
      cases h
      unfold parseString at hps
      split at hps
      · rename_i x hx
        cases hps
        exact (strScan_err hx).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
      · split at hps
        · cases hps; exact Or.inl rfl
        · cases hps
    · cases h
  rw [ite_eq_right h3] at h
  by_cases h4 : c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32
  · rw [ite_eq_left h4] at h; cases h
  rw [ite_eq_right h4] at h
  by_cases h5 : c = 58
  · rw [ite_eq_left h5] at h; cases h
  rw [ite_eq_right h5] at h
  by_cases h6 : c = 44
  · rw [ite_eq_left h6] at h
    split at h <;> cases h
  rw [ite_eq_right h6] at h
  split at h
  · rename_i e' hpp
    cases h
    unfold parsePrimitive at hpp
    split at hpp
    · cases hpp; exact Or.inr (Or.inl rfl)
    · split at hpp
      · cases hpp; exact Or.inl rfl
      · cases hpp
  · cases h

theorem mainLoop_err {js : List Nat} {n : Nat} (st : St) {e : Int}
    (h : mainLoop js n st = .error e) : e = ERROR_NOMEM ∨ e = ERROR_INVAL ∨ e = ERROR_PART := by
  rw [mainLoop_eq] at h
  by_cases hl : live js st.pos
  · rw [ite_eq_left hl] at h
    cases hs : step js n st with
    | error e' => rw [hs] at h; cases h; exact step_err hs
    | ok st'' =>
      rw [hs] at h
      dsimp only at h
      exact mainLoop_err st'' h
  · rw [ite_eq_right hl] at h; cases h
termination_by js.length - st.pos
decreasing_by have := step_pos_lt hl hs; have := hl.1; omega

/-- **What `parse` returns**: an error code with no tokens, or the number of tokens, at most
`n` and at most the text's length, each token within the text and with `size` at most the
number of tokens. -/
theorem parse_cases (js : List Nat) (n : Nat) :
    (((parse js n).1 = ERROR_NOMEM ∨ (parse js n).1 = ERROR_INVAL ∨ (parse js n).1 = ERROR_PART) ∧
        (parse js n).2 = []) ∨
      ((parse js n).1 = (parse js n).2.length ∧ (parse js n).2.length ≤ n ∧
        (parse js n).2.length ≤ js.length ∧
        AllOk js.length (parse js n).2.length (parse js n).2) := by
  unfold parse
  split
  · rename_i e he
    exact Or.inl ⟨mainLoop_err St.init he, rfl⟩
  · rename_i st hst
    have hi := mainLoop_inv St.init (inv_init js n) hst
    split
    · exact Or.inl ⟨Or.inr (Or.inr rfl), rfl⟩
    · refine Or.inr ⟨rfl, hi.len_n, ?_, hi.toks.mono hi.pos_le (Nat.le_refl _)⟩
      have := hi.len_pos; have := hi.pos_le; dsimp only; omega

end EquivLean.Demo.XLang.Jsmn
