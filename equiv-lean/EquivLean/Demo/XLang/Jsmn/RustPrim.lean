import EquivLean.Demo.XLang.Jsmn.RustScan

/-!
# jsmn → model, Rust side: `parse_primitive` and `parse_string`

Each scan loop against the model's scan (`primScan`, `strScan`), one loop turn at a time; then
the two functions against `parsePrimitive` / `parseString` through `absSt`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas jsmn_rs

namespace EquivLean.Demo.XLang.Jsmn.Rust

/-! ## The source bytes -/

theorem length_bytes (js : Slice U8) : (bytes js).length = js.val.length := by
  simp [bytes]

theorem byteAt_bytes {js : Slice U8} {i : Nat} (h : i < js.val.length) :
    byteAt (bytes js) i = (js.val[i]'h).val := by
  simp [byteAt, bytes, List.getD_eq_getElem?_getD, h]

theorem live_bytes {js : Slice U8} {i : Nat} (h : i < js.val.length) :
    live (bytes js) i ↔ (js.val[i]'h).val ≠ 0 := by
  simp [live, length_bytes, h, byteAt_bytes h]

theorem lt_of_live {js : Slice U8} {i : Nat} (h : live (bytes js) i) : i < js.val.length := by
  have := h.1
  rwa [length_bytes] at this

/-- A token allocated (`a`) and then filled (`b`) at the free index `k`. -/
theorem mtoks_alloc_fill (ts : Slice JsmnTok) (k : Usize) (hk : k.val < ts.val.length) (a b : JsmnTok) :
    mtoks ((ts.set k a).set k b) (k.val + 1) = mtoks ts k.val ++ [toTok b] := by
  rw [mtoks_set_eq k b (by simp [Slice.set_val_eq]; exact hk), mtoks_set_ge k a (le_refl _)]

/-! ## `parse_primitive` -/

theorem prim_body_found (js : Slice U8) (len s : Usize) (inval : Bool) :
    parse_primitive_loop.body js len s true inval = .ok (.done (s, inval)) := rfl

theorem prim_body_inval (js : Slice U8) (len s : Usize) :
    parse_primitive_loop.body js len s false true = .ok (.done (s, true)) := rfl

theorem prim_body_end {js : Slice U8} {s : Usize} (h : ¬ live (bytes js) s.val) :
    parse_primitive_loop.body js (Slice.len js) s false false = .ok (.done (s, false)) := by
  by_cases hl : s.val < js.val.length
  · have hz : (js.val[s.val]'hl).val = 0 := by
      rw [live_bytes hl] at h
      omega
    apply eq_ok_of_wp
    unfold parse_primitive_loop.body
    aeneas_wp
    rust_split
    all_goals try (exfalso; omega)
    all_goals try contradiction
    all_goals simp
  · apply eq_ok_of_wp
    unfold parse_primitive_loop.body
    aeneas_wp
    rust_split
    all_goals try (exfalso; omega)
    all_goals try contradiction
    all_goals simp

theorem prim_body_delim {js : Slice U8} {s : Usize} (hl : s.val < js.val.length)
    (hz : (js.val[s.val]'hl).val ≠ 0) (hd : primDelim (js.val[s.val]'hl).val = true) :
    parse_primitive_loop.body js (Slice.len js) s false false = .ok (.cont (s, true, false)) := by
  simp only [primDelim, Bool.or_eq_true, beq_iff_eq] at hd
  apply eq_ok_of_wp
  unfold parse_primitive_loop.body
  aeneas_wp
  rust_split
  all_goals try (exfalso; omega)
  all_goals try contradiction
  all_goals simp

theorem prim_body_bad {js : Slice U8} {s : Usize} (hl : s.val < js.val.length)
    (hz : (js.val[s.val]'hl).val ≠ 0) (hd : primDelim (js.val[s.val]'hl).val = false)
    (hb : (js.val[s.val]'hl).val < 32 ∨ 127 ≤ (js.val[s.val]'hl).val) :
    parse_primitive_loop.body js (Slice.len js) s false false = .ok (.cont (s, false, true)) := by
  simp only [primDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hd
  apply eq_ok_of_wp
  unfold parse_primitive_loop.body
  aeneas_wp
  rust_split
  all_goals try (exfalso; omega)
  all_goals try contradiction
  all_goals simp

theorem prim_body_next {js : Slice U8} {s : Usize} (hl : s.val < js.val.length)
    (hz : (js.val[s.val]'hl).val ≠ 0) (hd : primDelim (js.val[s.val]'hl).val = false)
    (hb : ¬ ((js.val[s.val]'hl).val < 32 ∨ 127 ≤ (js.val[s.val]'hl).val)) :
    ∃ c, parse_primitive_loop.body js (Slice.len js) s false false = .ok c ∧
      ∃ s' : Usize, c = .cont (s', false, false) ∧ s'.val = s.val + 1 := by
  simp only [primDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hd
  have hmax := js.property
  apply exists_ok_of_wp
  unfold parse_primitive_loop.body
  aeneas_wp
  rust_split
  all_goals try (exfalso; omega)
  all_goals try contradiction
  all_goals simp

theorem prim_loop_eq (js : Slice U8) :
    ∀ (m : Nat) (s : Usize), js.val.length - s.val = m → s.val ≤ js.val.length →
      ∃ r, parse_primitive_loop s js (Slice.len js) false false = .ok r ∧
        s.val ≤ r.1.val ∧ r.1.val ≤ js.val.length ∧
        (match primScan (bytes js) s.val with
         | none => r.2 = true
         | some e => r.2 = false ∧ r.1.val = e) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro s hm hs
  by_cases hlive : live (bytes js) s.val
  · have hl := lt_of_live hlive
    have hz : (js.val[s.val]'hl).val ≠ 0 := (live_bytes hl).1 hlive
    have hps : primScan (bytes js) s.val =
        if primDelim (js.val[s.val]'hl).val then some s.val
        else if (js.val[s.val]'hl).val < 32 ∨ 127 ≤ (js.val[s.val]'hl).val then none
        else primScan (bytes js) (s.val + 1) := by
      rw [primScan, dif_pos hlive, byteAt_bytes hl]
    by_cases hd : primDelim (js.val[s.val]'hl).val = true
    · refine ⟨(s, false), ?_, le_refl _, hs, ?_⟩
      · unfold parse_primitive_loop
        rw [loop_cont (prim_body_delim hl hz hd)]
        exact loop_done (prim_body_found js _ s false)
      · rw [hps, if_pos hd]
        exact ⟨rfl, rfl⟩
    · have hd' : primDelim (js.val[s.val]'hl).val = false := by simpa using hd
      by_cases hb : (js.val[s.val]'hl).val < 32 ∨ 127 ≤ (js.val[s.val]'hl).val
      · refine ⟨(s, true), ?_, le_refl _, hs, ?_⟩
        · unfold parse_primitive_loop
          rw [loop_cont (prim_body_bad hl hz hd' hb)]
          exact loop_done (prim_body_inval js _ s)
        · rw [hps, if_neg hd, if_pos hb]
      · obtain ⟨c, hc, s', rfl, hs'⟩ := prim_body_next hl hz hd' hb
        obtain ⟨r, hr, hr1, hr2, hr3⟩ := IH (js.val.length - s'.val) (by omega) s' rfl (by omega)
        refine ⟨r, ?_, by omega, hr2, ?_⟩
        · unfold parse_primitive_loop at hr ⊢
          rw [loop_cont hc]
          exact hr
        · rw [hps, if_neg hd, if_neg hb, ← hs']
          exact hr3
  · refine ⟨(s, false), ?_, le_refl _, hs, ?_⟩
    · unfold parse_primitive_loop
      exact loop_done (prim_body_end hlive)
    · rw [primScan, dif_neg hlive]
      exact ⟨rfl, rfl⟩

/-- `jsmn_parse_primitive` on a primitive's first byte (live, not a delimiter): the model's
`parsePrimitive`, with the error codes as return values. -/
theorem parse_primitive_spec {p : JsmnParser} {js : Slice U8} {ts : Slice JsmnTok}
    (hl : p.pos.val < js.val.length) (hlen : js.val.length < 2 ^ 28)
    (hz : (js.val[p.pos.val]'hl).val ≠ 0) (hd : primDelim (js.val[p.pos.val]'hl).val = false)
    (hk : p.toknext.val ≤ ts.val.length) :
    ∃ v, parse_primitive p js ts = .ok v ∧
      match parsePrimitive (bytes js) ts.val.length (absSt p ts) with
      | .error e => v.1.val = e ∧ e < 0
      | .ok st' => v.1.val = 0 ∧ absSt v.2.1 v.2.2 = st' ∧ v.2.1.toknext.val = p.toknext.val + 1 ∧
          v.2.1.toksuper = p.toksuper ∧ v.2.2.val.length = ts.val.length ∧
          p.toknext.val < ts.val.length ∧ p.pos.val ≤ v.2.1.pos.val ∧ v.2.1.pos.val < js.val.length := by
  have hlive : live (bytes js) p.pos.val := (live_bytes hl).2 hz
  have hps0 : primScan (bytes js) p.pos.val =
      if (js.val[p.pos.val]'hl).val < 32 ∨ 127 ≤ (js.val[p.pos.val]'hl).val then none
      else primScan (bytes js) (p.pos.val + 1) := by
    rw [primScan, dif_pos hlive, byteAt_bytes hl]
    simp [hd]
  by_cases hb : (js.val[p.pos.val]'hl).val < 32 ∨ 127 ≤ (js.val[p.pos.val]'hl).val
  · -- a byte outside `32 .. 126`: `JSMN_ERROR_INVAL`
    have hloop : parse_primitive_loop p.pos js (Slice.len js) false false = .ok (p.pos, true) := by
      unfold parse_primitive_loop
      rw [loop_cont (prim_body_bad hl hz hd hb)]
      exact loop_done (prim_body_inval js _ p.pos)
    have hm : parsePrimitive (bytes js) ts.val.length (absSt p ts) = .error ERROR_INVAL := by
      simp only [parsePrimitive, absSt, hps0, if_pos hb]
    rw [hm]
    refine ⟨(JSMN_ERROR_INVAL, p, ts), ?_, ?_⟩
    · apply eq_ok_of_wp
      unfold parse_primitive
      aeneas_wp [hloop]
    · simp [JSMN_ERROR_INVAL, ERROR_INVAL]
  · obtain ⟨c, hc, s', rfl, hs'⟩ := prim_body_next hl hz hd hb
    obtain ⟨⟨i, inval⟩, hr, hr1, hr2, hr3⟩ := prim_loop_eq js _ s' rfl (by omega)
    have hloop : parse_primitive_loop p.pos js (Slice.len js) false false = .ok (i, inval) := by
      unfold parse_primitive_loop at hr ⊢
      rw [loop_cont hc]
      exact hr
    have hps : primScan (bytes js) p.pos.val = primScan (bytes js) s'.val := by
      rw [hps0, if_neg hb, hs']
    cases hsc : primScan (bytes js) s'.val with
    | none =>
      rw [hsc] at hr3
      simp only at hr3
      subst hr3
      have hm : parsePrimitive (bytes js) ts.val.length (absSt p ts) = .error ERROR_INVAL := by
        simp only [parsePrimitive, absSt, hps, hsc]
      rw [hm]
      refine ⟨(JSMN_ERROR_INVAL, p, ts), ?_, ?_⟩
      · apply eq_ok_of_wp
        unfold parse_primitive
        aeneas_wp [hloop]
      · simp [JSMN_ERROR_INVAL, ERROR_INVAL]
    | some e =>
      rw [hsc] at hr3
      obtain ⟨rfl, hie⟩ := hr3
      simp only at hr1 hr2 hie
      subst hie
      by_cases hfull : ts.val.length ≤ p.toknext.val
      · -- the array is full: `JSMN_ERROR_NOMEM`
        have ha := alloc_token_none (p := { p with pos := i }) (ts := ts) hfull
        have hm : parsePrimitive (bytes js) ts.val.length (absSt p ts) = .error ERROR_NOMEM := by
          simp only [parsePrimitive, absSt, hps, hsc, mtoks_length hk, if_pos hfull]
        rw [hm]
        refine ⟨(JSMN_ERROR_NOMEM, ⟨p.pos, p.toknext, p.toksuper⟩, ts), ?_, ?_⟩
        · apply eq_ok_of_wp
          unfold parse_primitive
          aeneas_wp [hloop, ha, Bool.false_eq_true]
        · simp [JSMN_ERROR_NOMEM, ERROR_NOMEM]
      · have hlt : p.toknext.val < ts.val.length := by omega
        obtain ⟨a, ha, ha1, ha2, ha3, ha4, ha5⟩ :=
          alloc_token_some (p := { p with pos := i }) (ts := ts) hlt
        obtain ⟨o, p1, ts1⟩ := a
        simp only at ha1 ha2 ha3 ha4 ha5
        subst ha1 ha5 ha2
        have hm : parsePrimitive (bytes js) ts.val.length (absSt p ts) =
            .ok ⟨p1.pos.val - 1, mtoks ts p.toknext.val ++ [⟨PRIMITIVE, p.pos.val, p1.pos.val, 0⟩],
              p.toksuper.val⟩ := by
          simp only [parsePrimitive, absSt, hps, hsc, mtoks_length hk, if_neg hfull]
        rw [hm]
        have hc1 := hcast_i32_val (x := p.pos) (by omega)
        have hc2 := hcast_i32_val (x := p1.pos) (by omega)
        apply exists_ok_of_wp
        unfold parse_primitive
        aeneas_wp [hloop, ha, slice_index_mut_usize_eq, fill_token_eq, Slice.set_val_eq,
          List.length_set]
        rust_split
        all_goals try contradiction
        all_goals try (exfalso; omega)
        refine ⟨_, rfl, rfl, ?_, ha3, by rw [ha4], by simp [Slice.set_val_eq], hlt,
          by simp only [UScalar.ofNatCore_val_eq]; omega, by simp only [UScalar.ofNatCore_val_eq]; omega⟩
        simp only [absSt, St.mk.injEq]
        refine ⟨by simp, ?_, by rw [ha4]⟩
        rw [ha3, mtoks_alloc_fill ts p.toknext hlt]
        simp [toTok, typeCode, hc1, hc2]

/-! ## `parse_string` -/

theorem strScan_dead {js : List Nat} {p : Nat} (hex : Nat) (h : ¬ live js p) :
    strScan js p hex = .error ERROR_PART := by
  rw [strScan, dif_neg h]

theorem strScan_hex {js : List Nat} {p hex : Nat} (h : live js p) (hx : 0 < hex) :
    strScan js p hex =
      if hexDigit (byteAt js p) then strScan js (p + 1) (hex - 1) else .error ERROR_INVAL := by
  rw [strScan, dif_pos h]
  simp [hx]

theorem strScan_zero {js : List Nat} {p : Nat} (h : live js p) :
    strScan js p 0 =
      if byteAt js p = 34 then .ok p
      else if byteAt js p = 92 ∧ p + 1 < js.length then
        (if escChar (byteAt js (p + 1)) then strScan js (p + 2) 0
         else if byteAt js (p + 1) = 117 then strScan js (p + 2) 4
         else .error ERROR_INVAL)
      else strScan js (p + 1) 0 := by
  rw [strScan, dif_pos h]
  first | rfl | simp

/-! ### The `\uXXXX` loop -/

theorem hex_body_bad (js : Slice U8) (len i : Usize) (c : I32) :
    parse_string_loop0_loop0.body js len i c true = .ok (.done (i, true)) := rfl

theorem hex_body_full {js : Slice U8} {i : Usize} {c : I32} (hc : 4 ≤ c.val) :
    parse_string_loop0_loop0.body js (Slice.len js) i c false = .ok (.done (i, false)) := by
  apply eq_ok_of_wp
  unfold parse_string_loop0_loop0.body
  aeneas_wp
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

theorem hex_body_end {js : Slice U8} {i : Usize} {c : I32} (h : ¬ live (bytes js) i.val) :
    parse_string_loop0_loop0.body js (Slice.len js) i c false = .ok (.done (i, false)) := by
  by_cases hl : i.val < js.val.length
  · have hz : (js.val[i.val]'hl).val = 0 := by
      rw [live_bytes hl] at h
      omega
    apply eq_ok_of_wp
    unfold parse_string_loop0_loop0.body
    aeneas_wp
    rust_split
    all_goals try contradiction
    all_goals try (exfalso; omega)
    all_goals simp
  · apply eq_ok_of_wp
    unfold parse_string_loop0_loop0.body
    aeneas_wp
    rust_split
    all_goals try contradiction
    all_goals try (exfalso; omega)
    all_goals simp

theorem hex_body_hex {js : Slice U8} {i : Usize} {c : I32} (hc : c.val < 4) (hc0 : 0 ≤ c.val)
    (hl : i.val < js.val.length) (hz : (js.val[i.val]'hl).val ≠ 0)
    (hh : hexDigit (js.val[i.val]'hl).val = true) :
    ∃ x, parse_string_loop0_loop0.body js (Slice.len js) i c false = .ok x ∧
      ∃ (i' : Usize) (c' : I32), x = .cont (i', c', false) ∧ i'.val = i.val + 1 ∧
        c'.val = c.val + 1 := by
  have hmax := js.property
  apply exists_ok_of_wp
  unfold parse_string_loop0_loop0.body
  aeneas_wp [is_hex_eq, hh]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

theorem hex_body_nonhex {js : Slice U8} {i : Usize} {c : I32} (hc : c.val < 4)
    (hl : i.val < js.val.length) (hz : (js.val[i.val]'hl).val ≠ 0)
    (hh : hexDigit (js.val[i.val]'hl).val = false) :
    parse_string_loop0_loop0.body js (Slice.len js) i c false = .ok (.cont (i, c, true)) := by
  apply eq_ok_of_wp
  unfold parse_string_loop0_loop0.body
  aeneas_wp [is_hex_eq, hh]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

/-- The `\uXXXX` loop with `hx` digits still to read: `strScan`'s `hx` digits. -/
theorem hex_loop_eq (js : Slice U8) :
    ∀ (hx : Nat) (i : Usize) (c : I32), hx ≤ 4 → c.val = 4 - (hx : Int) → i.val ≤ js.val.length →
      ∃ r, parse_string_loop0_loop0 i js (Slice.len js) c false = .ok r ∧
        i.val ≤ r.1.val ∧ r.1.val ≤ js.val.length ∧
        (if r.2 then strScan (bytes js) i.val hx = .error ERROR_INVAL
         else strScan (bytes js) i.val hx = strScan (bytes js) r.1.val 0) := by
  intro hx
  induction hx with
  | zero =>
    intro i c _ hc hi
    refine ⟨(i, false), ?_, le_refl _, hi, ?_⟩
    · unfold parse_string_loop0_loop0
      exact loop_done (hex_body_full (by omega))
    · show strScan (bytes js) i.val 0 = strScan (bytes js) i.val 0
      rfl
  | succ hx IH =>
    intro i c hx4 hc hi
    by_cases hlive : live (bytes js) i.val
    · have hl := lt_of_live hlive
      have hz : (js.val[i.val]'hl).val ≠ 0 := (live_bytes hl).1 hlive
      have hs := strScan_hex (hex := hx + 1) hlive (by omega)
      rw [byteAt_bytes hl] at hs
      by_cases hh : hexDigit (js.val[i.val]'hl).val = true
      · obtain ⟨x, hx1, i', c', rfl, hi', hc'⟩ := hex_body_hex (c := c) (by omega) (by omega) hl hz hh
        obtain ⟨r, hr, hr1, hr2, hr3⟩ := IH i' c' (by omega) (by omega) (by omega)
        refine ⟨r, ?_, by omega, hr2, ?_⟩
        · unfold parse_string_loop0_loop0 at hr ⊢
          rw [loop_cont hx1]
          exact hr
        · rw [hs, if_pos hh, Nat.add_sub_cancel, ← hi']
          exact hr3
      · have hh' : hexDigit (js.val[i.val]'hl).val = false := by simpa using hh
        refine ⟨(i, true), ?_, le_refl _, hi, ?_⟩
        · unfold parse_string_loop0_loop0
          rw [loop_cont (hex_body_nonhex (c := c) (by omega) hl hz hh')]
          exact loop_done (hex_body_bad js _ i c)
        · show strScan (bytes js) i.val (hx + 1) = .error ERROR_INVAL
          rw [hs, if_neg hh]
    · refine ⟨(i, false), ?_, le_refl _, hi, ?_⟩
      · unfold parse_string_loop0_loop0
        exact loop_done (hex_body_end hlive)
      · show strScan (bytes js) i.val (hx + 1) = strScan (bytes js) i.val 0
        rw [strScan_dead _ hlive, strScan_dead _ hlive]

/-- `hex_loop_eq` from a `\u`, as a `wp` rule (the start index is a computed term). -/
theorem hex_loop_wp (js : Slice U8) (X : Usize) (hX : X.val ≤ js.val.length)
    {Q : Except Error (Usize × Bool) → Prop}
    (hq : ∀ r : Usize × Bool, X.val ≤ r.1.val → r.1.val ≤ js.val.length →
      (if r.2 then strScan (bytes js) X.val 4 = .error ERROR_INVAL
       else strScan (bytes js) X.val 4 = strScan (bytes js) r.1.val 0) → Q (.ok r)) :
    wp (parse_string_loop0_loop0 X js (Slice.len js) 0#i32 false) Q := by
  obtain ⟨r, hr, h1, h2, h3⟩ := hex_loop_eq js 4 X 0#i32 (le_refl _) (by simp) hX
  rw [hr, wp_ok]
  exact hq r h1 h2 h3

/-! ### The string loop -/

theorem str_body_done (js : Slice U8) (len start i k : Usize) (sup : I32) (ts : Slice JsmnTok)
    (res : I32) :
    parse_string_loop0.body js len start i k sup ts res true =
      .ok (.done (i, k, sup, ts, res, true)) := rfl

theorem str_body_end {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok} {res : I32}
    (h : ¬ live (bytes js) i.val) :
    parse_string_loop0.body js (Slice.len js) start i k sup ts res false =
      .ok (.done (i, k, sup, ts, res, false)) := by
  by_cases hl : i.val < js.val.length
  · have hz : (js.val[i.val]'hl).val = 0 := by
      rw [live_bytes hl] at h
      omega
    apply eq_ok_of_wp
    unfold parse_string_loop0.body
    aeneas_wp
    rust_split
    all_goals try contradiction
    all_goals try (exfalso; omega)
    all_goals simp
  · apply eq_ok_of_wp
    unfold parse_string_loop0.body
    aeneas_wp
    rust_split
    all_goals try contradiction
    all_goals try (exfalso; omega)
    all_goals simp

theorem str_body_quote_full {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hq : (js.val[i.val]'hl).val = 34)
    (hfull : ts.val.length ≤ k.val) :
    parse_string_loop0.body js (Slice.len js) start i k sup ts res false =
      .ok (.cont (start, k, sup, ts, JSMN_ERROR_NOMEM, true)) := by
  have ha := alloc_token_none (p := ⟨i, k, sup⟩) (ts := ts) hfull
  apply eq_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp [ha]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

theorem str_body_quote_ok {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hq : (js.val[i.val]'hl).val = 34)
    (hlt : k.val < ts.val.length) (hlen : js.val.length < 2 ^ 28) (hs : start.val < i.val) :
    ∃ x, parse_string_loop0.body js (Slice.len js) start i k sup ts res false = .ok x ∧
      ∃ (k' : Usize) (ts' : Slice JsmnTok), x = .cont (i, k', sup, ts', 0#i32, true) ∧
        k'.val = k.val + 1 ∧
        mtoks ts' (k.val + 1) = mtoks ts k.val ++ [⟨STRING, start.val + 1, i.val, 0⟩] ∧
        ts'.val.length = ts.val.length := by
  obtain ⟨a, ha, ha1, ha2, ha3, ha4, ha5⟩ := alloc_token_some (p := ⟨i, k, sup⟩) (ts := ts) hlt
  obtain ⟨o, p1, ts1⟩ := a
  simp only at ha1 ha2 ha3 ha4 ha5
  subst ha1 ha5 ha2 ha4
  have hc1 := hcast_i32_val (x := start) (by omega)
  have hc2 := hcast_i32_val (x := p1.pos) (by omega)
  apply exists_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp [ha, slice_index_mut_usize_eq, fill_token_eq, Slice.set_val_eq, List.length_set, hc1,
    hl, hq]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  refine ⟨_, rfl, _, _, rfl, ha3, ?_, by simp [Slice.set_val_eq]⟩
  rw [mtoks_alloc_fill ts k hlt]
  simp [toTok, typeCode, hc1, hc2]

theorem str_body_esc_simple {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hb : (js.val[i.val]'hl).val = 92)
    (hl1 : i.val + 1 < js.val.length) (he : escChar (js.val[i.val + 1]'hl1).val = true) :
    ∃ x, parse_string_loop0.body js (Slice.len js) start i k sup ts res false = .ok x ∧
      ∃ i' : Usize, x = .cont (i', k, sup, ts, res, false) ∧ i'.val = i.val + 2 := by
  have hmax := js.property
  apply exists_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp [is_simple_escape_eq, he]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

theorem str_body_esc_u {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hb : (js.val[i.val]'hl).val = 92)
    (hl1 : i.val + 1 < js.val.length) (he : escChar (js.val[i.val + 1]'hl1).val = false)
    (hu : (js.val[i.val + 1]'hl1).val = 117) :
    ∃ x, parse_string_loop0.body js (Slice.len js) start i k sup ts res false = .ok x ∧
      ∃ (X j : Usize) (bad : Bool), X.val = i.val + 2 ∧ X.val ≤ j.val ∧ j.val ≤ js.val.length ∧
        (if bad then strScan (bytes js) X.val 4 = .error ERROR_INVAL
         else strScan (bytes js) X.val 4 = strScan (bytes js) j.val 0) ∧
        x = (if bad then .cont (start, k, sup, ts, JSMN_ERROR_INVAL, true)
             else .cont (j, k, sup, ts, res, false)) := by
  have hmax := js.property
  apply exists_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp [is_simple_escape_eq, he, Bool.false_eq_true]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals refine hex_loop_wp js _ (by simp only [UScalar.ofNatCore_val_eq]; omega) ?_
  all_goals rintro ⟨j, bad⟩ h1 h2 h3
  all_goals cases bad
  all_goals aeneas_wp
  all_goals first
    | exact ⟨_, rfl, _, j, false, by simp only [UScalar.ofNatCore_val_eq], h1, h2, h3, rfl⟩
    | exact ⟨_, rfl, _, j, true, by simp only [UScalar.ofNatCore_val_eq], h1, h2, h3, rfl⟩

theorem str_body_esc_bad {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hb : (js.val[i.val]'hl).val = 92)
    (hl1 : i.val + 1 < js.val.length) (he : escChar (js.val[i.val + 1]'hl1).val = false)
    (hu : (js.val[i.val + 1]'hl1).val ≠ 117) :
    parse_string_loop0.body js (Slice.len js) start i k sup ts res false =
      .ok (.cont (start, k, sup, ts, JSMN_ERROR_INVAL, true)) := by
  have hmax := js.property
  apply eq_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp [is_simple_escape_eq, he, Bool.false_eq_true]
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

theorem str_body_other {js : Slice U8} {start i k : Usize} {sup : I32} {ts : Slice JsmnTok}
    {res : I32} (hl : i.val < js.val.length) (hz : (js.val[i.val]'hl).val ≠ 0)
    (hq : (js.val[i.val]'hl).val ≠ 34)
    (hb : ¬ ((js.val[i.val]'hl).val = 92 ∧ i.val + 1 < js.val.length)) :
    ∃ x, parse_string_loop0.body js (Slice.len js) start i k sup ts res false = .ok x ∧
      ∃ i' : Usize, x = .cont (i', k, sup, ts, res, false) ∧ i'.val = i.val + 1 := by
  have hmax := js.property
  apply exists_ok_of_wp
  unfold parse_string_loop0.body
  aeneas_wp
  rust_split
  all_goals try contradiction
  all_goals try (exfalso; omega)
  all_goals simp

/-- What the string loop leaves for the model's scan outcome `o`: the error code, or the new
`JSMN_STRING` token (or `JSMN_ERROR_NOMEM` when the array is full). -/
def StrPost (js : Slice U8) (ts : Slice JsmnTok) (k : Usize) (sup : I32) (start : Usize)
    (o : Except Int Nat) (r : Usize × Usize × I32 × Slice JsmnTok × I32 × Bool) : Prop :=
  match o with
  | .error e => r.2.2.2.2.1.val = e ∧ e < 0
  | .ok q =>
    if ts.val.length ≤ k.val then r.2.2.2.2.1 = JSMN_ERROR_NOMEM
    else r.2.2.2.2.2 = true ∧ r.2.2.2.2.1 = 0#i32 ∧ r.1.val = q ∧ r.2.1.val = k.val + 1 ∧
      r.2.2.1 = sup ∧ mtoks r.2.2.2.1 (k.val + 1) = mtoks ts k.val ++ [⟨STRING, start.val + 1, q, 0⟩] ∧
      r.2.2.2.1.val.length = ts.val.length ∧ q < js.val.length ∧ start.val < q

theorem str_loop_eq (js : Slice U8) (hlen : js.val.length < 2 ^ 28) (start k : Usize) (sup : I32)
    (ts : Slice JsmnTok) :
    ∀ (m : Nat) (i : Usize), js.val.length - i.val = m → start.val < i.val → i.val ≤ js.val.length →
      ∃ r, parse_string_loop0 i k sup js ts (Slice.len js) start JSMN_ERROR_PART false = .ok r ∧
        StrPost js ts k sup start (strScan (bytes js) i.val 0) r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro i hm hs hi
  by_cases hlive : live (bytes js) i.val
  · have hl := lt_of_live hlive
    have hz : (js.val[i.val]'hl).val ≠ 0 := (live_bytes hl).1 hlive
    have hs0 := strScan_zero hlive
    rw [byteAt_bytes hl, length_bytes] at hs0
    by_cases hq : (js.val[i.val]'hl).val = 34
    · rw [if_pos hq] at hs0
      rw [hs0]
      by_cases hfull : ts.val.length ≤ k.val
      · refine ⟨(start, k, sup, ts, JSMN_ERROR_NOMEM, true), ?_, ?_⟩
        · unfold parse_string_loop0
          rw [loop_cont (str_body_quote_full hl hq hfull)]
          exact loop_done (str_body_done js _ start start k sup ts _)
        · simp only [StrPost, if_pos hfull]
      · obtain ⟨x, hx, k', ts', rfl, hk', hts', hlen'⟩ :=
          str_body_quote_ok (start := start) (k := k) (sup := sup) (ts := ts) (res := JSMN_ERROR_PART)
            hl hq (by omega) hlen hs
        refine ⟨(i, k', sup, ts', 0#i32, true), ?_, ?_⟩
        · unfold parse_string_loop0
          rw [loop_cont hx]
          exact loop_done (str_body_done js _ start i k' sup ts' _)
        · simp [StrPost, hfull, hk', hts', hlen', hl, hs]
    · rw [if_neg hq] at hs0
      by_cases hb : (js.val[i.val]'hl).val = 92 ∧ i.val + 1 < js.val.length
      · rw [if_pos hb] at hs0
        have hl1 := hb.2
        rw [byteAt_bytes hl1] at hs0
        by_cases he : escChar (js.val[i.val + 1]'hl1).val = true
        · rw [if_pos he] at hs0
          obtain ⟨x, hx, i', rfl, hi'⟩ := str_body_esc_simple (start := start) (k := k) (sup := sup)
            (ts := ts) (res := JSMN_ERROR_PART) hl hb.1 hl1 he
          obtain ⟨r, hr, hpost⟩ := IH (js.val.length - i'.val) (by omega) i' rfl (by omega) (by omega)
          refine ⟨r, ?_, ?_⟩
          · unfold parse_string_loop0 at hr ⊢
            rw [loop_cont hx]
            exact hr
          · rw [hs0, ← hi']
            exact hpost
        · have he' : escChar (js.val[i.val + 1]'hl1).val = false := by simpa using he
          rw [if_neg he] at hs0
          by_cases hu : (js.val[i.val + 1]'hl1).val = 117
          · rw [if_pos hu] at hs0
            obtain ⟨x, hx, X, j, bad, hX, hj1, hj2, hj3, rfl⟩ := str_body_esc_u (start := start)
              (k := k) (sup := sup) (ts := ts) (res := JSMN_ERROR_PART) hl hb.1 hl1 he' hu
            rw [hX] at hj3
            cases bad with
            | true =>
              refine ⟨(start, k, sup, ts, JSMN_ERROR_INVAL, true), ?_, ?_⟩
              · unfold parse_string_loop0
                rw [loop_cont hx]
                exact loop_done (str_body_done js _ start start k sup ts _)
              · have hj3' : strScan (bytes js) (i.val + 2) 4 = .error ERROR_INVAL := hj3
                rw [hs0, hj3']
                simp [StrPost, JSMN_ERROR_INVAL, ERROR_INVAL]
            | false =>
              have hj3' : strScan (bytes js) (i.val + 2) 4 = strScan (bytes js) j.val 0 := hj3
              obtain ⟨r, hr, hpost⟩ := IH (js.val.length - j.val) (by omega) j rfl (by omega) hj2
              refine ⟨r, ?_, ?_⟩
              · unfold parse_string_loop0 at hr ⊢
                rw [loop_cont hx]
                exact hr
              · rw [hs0, hj3']
                exact hpost
          · rw [if_neg hu] at hs0
            refine ⟨(start, k, sup, ts, JSMN_ERROR_INVAL, true), ?_, ?_⟩
            · unfold parse_string_loop0
              rw [loop_cont (str_body_esc_bad hl hb.1 hl1 he' hu)]
              exact loop_done (str_body_done js _ start start k sup ts _)
            · rw [hs0]
              simp [StrPost, JSMN_ERROR_INVAL, ERROR_INVAL]
      · rw [if_neg hb] at hs0
        obtain ⟨x, hx, i', rfl, hi'⟩ := str_body_other (start := start) (k := k) (sup := sup)
          (ts := ts) (res := JSMN_ERROR_PART) hl hz hq hb
        obtain ⟨r, hr, hpost⟩ := IH (js.val.length - i'.val) (by omega) i' rfl (by omega) (by omega)
        refine ⟨r, ?_, ?_⟩
        · unfold parse_string_loop0 at hr ⊢
          rw [loop_cont hx]
          exact hr
        · rw [hs0, ← hi']
          exact hpost
  · refine ⟨(i, k, sup, ts, JSMN_ERROR_PART, false), ?_, ?_⟩
    · unfold parse_string_loop0
      exact loop_done (str_body_end hlive)
    · rw [strScan_dead _ hlive]
      simp [StrPost, JSMN_ERROR_PART, ERROR_PART]

/-- `str_loop_eq` as a `wp` rule (the start index is a computed term). -/
theorem str_loop_wp (js : Slice U8) (hlen : js.val.length < 2 ^ 28) (start k : Usize) (sup : I32)
    (ts : Slice JsmnTok) (X : Usize) (hX1 : start.val < X.val) (hX2 : X.val ≤ js.val.length)
    {Q : Except Error (Usize × Usize × I32 × Slice JsmnTok × I32 × Bool) → Prop}
    (hq : ∀ r, StrPost js ts k sup start (strScan (bytes js) X.val 0) r → Q (.ok r)) :
    wp (parse_string_loop0 X k sup js ts (Slice.len js) start JSMN_ERROR_PART false) Q := by
  obtain ⟨r, hr, h⟩ := str_loop_eq js hlen start k sup ts _ X rfl hX1 hX2
  rw [hr, wp_ok]
  exact hq r h

/-- `jsmn_parse_string` at an opening quote: the model's `parseString`, with the error codes as
return values. -/
theorem parse_string_spec {p : JsmnParser} {js : Slice U8} {ts : Slice JsmnTok}
    (hl : p.pos.val < js.val.length) (hlen : js.val.length < 2 ^ 28)
    (hk : p.toknext.val ≤ ts.val.length) :
    ∃ v, parse_string p js ts = .ok v ∧
      match parseString (bytes js) ts.val.length (absSt p ts) with
      | .error e => v.1.val = e ∧ e < 0
      | .ok st' => v.1.val = 0 ∧ absSt v.2.1 v.2.2 = st' ∧ v.2.1.toknext.val = p.toknext.val + 1 ∧
          v.2.1.toksuper = p.toksuper ∧ v.2.2.val.length = ts.val.length ∧
          p.toknext.val < ts.val.length ∧ p.pos.val < v.2.1.pos.val ∧ v.2.1.pos.val < js.val.length := by
  have hmax := js.property
  cases ho : strScan (bytes js) (p.pos.val + 1) 0 with
  | error e =>
    have hm : parseString (bytes js) ts.val.length (absSt p ts) = .error e := by
      simp only [parseString, absSt, ho]
    rw [hm]
    apply exists_ok_of_wp
    unfold parse_string
    aeneas_wp
    rust_split
    all_goals try (exfalso; omega)
    refine str_loop_wp js hlen p.pos p.toknext p.toksuper ts _ (by simp) (by simp; omega) ?_
    rintro ⟨i1, i2, i3, ts1, res, done1⟩ hpost
    simp only [UScalar.ofNatCore_val_eq, ho, StrPost] at hpost
    aeneas_wp
    rust_split
    all_goals exact ⟨_, rfl, hpost⟩
  | ok q =>
    by_cases hfull : ts.val.length ≤ p.toknext.val
    · have hm : parseString (bytes js) ts.val.length (absSt p ts) = .error ERROR_NOMEM := by
        simp only [parseString, absSt, ho, mtoks_length hk, if_pos hfull]
      rw [hm]
      apply exists_ok_of_wp
      unfold parse_string
      aeneas_wp
      rust_split
      all_goals try (exfalso; omega)
      refine str_loop_wp js hlen p.pos p.toknext p.toksuper ts _ (by simp) (by simp; omega) ?_
      rintro ⟨i1, i2, i3, ts1, res, done1⟩ hpost
      simp only [UScalar.ofNatCore_val_eq, ho, StrPost, if_pos hfull] at hpost
      subst hpost
      aeneas_wp
      rust_split
      all_goals exact ⟨_, rfl, by simp [JSMN_ERROR_NOMEM, ERROR_NOMEM]⟩
    · have hm : parseString (bytes js) ts.val.length (absSt p ts) =
          .ok ⟨q, mtoks ts p.toknext.val ++ [⟨STRING, p.pos.val + 1, q, 0⟩], p.toksuper.val⟩ := by
        simp only [parseString, absSt, ho, mtoks_length hk, if_neg hfull]
      rw [hm]
      apply exists_ok_of_wp
      unfold parse_string
      aeneas_wp
      rust_split
      all_goals try (exfalso; omega)
      refine str_loop_wp js hlen p.pos p.toknext p.toksuper ts _ (by simp) (by simp; omega) ?_
      rintro ⟨i1, i2, i3, ts1, res, done1⟩ hpost
      simp only [UScalar.ofNatCore_val_eq, ho, StrPost, if_neg hfull] at hpost
      obtain ⟨rfl, rfl, hq1, hk2, rfl, hts, hlen1, hq2, hq3⟩ := hpost
      aeneas_wp
      refine ⟨_, rfl, rfl, ?_, hk2, rfl, hlen1, by omega, ?_, ?_⟩
      · show (⟨i1.val, mtoks ts1 i2.val, p.toksuper.val⟩ : St) = _
        rw [hq1, hk2, hts]
      · show p.pos.val < i1.val
        omega
      · show i1.val < js.val.length
        omega

end EquivLean.Demo.XLang.Jsmn.Rust
