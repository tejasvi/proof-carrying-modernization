import EquivLean.Demo.XLang.Jsmn.RustStep

/-!
# jsmn → model, Rust side: `jsmn_parse` computes the model

`main_loop_eq`: `jsmn_parse`'s loop against the model's `mainLoop` (induction on the bytes left);
`jsmn_parse_spec`: one call from a fresh parser against `parse`; `rust_spec`: for every input
shorter than `2^28` bytes the Rust run (`rustRun`) returns, and its observation is the model's.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas jsmn_rs

namespace EquivLean.Demo.XLang.Jsmn.Rust

/-- What `jsmn_parse`'s loop leaves, against the model's `mainLoop` outcome. -/
def LoopPost (js : Slice U8) (n : Nat) (o : Except Int St)
    (v : JsmnParser × Slice JsmnTok × I32 × I32 × Bool) : Prop :=
  match o with
  | .error e => v.2.2.2.2 = true ∧ v.2.2.2.1.val = e ∧ e < 0
  | .ok st => v.2.2.2.2 = false ∧ absSt v.1 v.2.1 = st ∧ Inv js v.1 v.2.1 v.2.2.1 ∧
      v.2.1.val.length = n

theorem main_loop_eq (js : Slice U8) :
    ∀ (m : Nat) (p : JsmnParser) (ts : Slice JsmnTok) (count ret : I32),
      js.val.length - p.pos.val = m → Inv js p ts count →
      ∃ v, jsmn_parse_loop p js ts (Slice.len js) count ret false = .ok v ∧
        LoopPost js ts.val.length (mainLoop (bytes js) ts.val.length (absSt p ts)) v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro p ts count ret hm hinv
  by_cases hlive : live (bytes js) p.pos.val
  · have hlive' : live (bytes js) (absSt p ts).pos := hlive
    have hl := lt_of_live hlive
    obtain ⟨⟨p', ts', count', ret', stop'⟩, hv, hpost⟩ := body_step (ret := ret) hinv hlive
    rw [mainLoop, dif_pos hlive']
    cases hs : step (bytes js) ts.val.length (absSt p ts) with
    | error e =>
      rw [hs] at hpost
      obtain ⟨hstop, hret, he⟩ := hpost
      dsimp only at hstop hret
      subst hstop
      refine ⟨(p', ts', count', ret', true), ?_, ⟨rfl, hret, he⟩⟩
      unfold jsmn_parse_loop
      rw [loop_cont hv]
      exact loop_done (body_stop _ (p', ts', count', ret'))
    | ok st' =>
      rw [hs] at hpost
      obtain ⟨hstop, habs, hinv', hlen', hpos'⟩ := hpost
      dsimp only at hstop habs hinv' hlen' hpos'
      subst hstop habs
      have hlt : (absSt p ts).pos < (absSt p' ts').pos := hpos'
      dsimp only
      rw [dif_pos hlt]
      obtain ⟨v2, hv2, hpost2⟩ :=
        IH (js.val.length - p'.pos.val) (by omega) p' ts' count' ret' rfl hinv'
      refine ⟨v2, ?_, ?_⟩
      · unfold jsmn_parse_loop at hv2 ⊢
        rw [loop_cont hv]
        exact hv2
      · rw [← hlen']
        exact hpost2
  · refine ⟨(p, ts, count, ret, false), ?_, ?_⟩
    · unfold jsmn_parse_loop
      exact loop_done (body_end hlive)
    · have hd : ¬ live (bytes js) (absSt p ts).pos := hlive
      rw [mainLoop, dif_neg hd]
      exact ⟨rfl, rfl, hinv, rfl⟩

/-- The final scan: no open token below `k` in the first `k` tokens iff none is open. -/
theorem lastOpen_none_iff (l : List Tok) :
    ∀ k, k ≤ l.length → (lastOpen l k = none ↔ (l.take k).any isOpen = false) := by
  intro k
  induction k with
  | zero => intro _; simp [lastOpen]
  | succ k IH =>
    intro hk
    have hk' : k < l.length := by omega
    have hg : l.getD k dflt = l[k]'hk' := by simp [List.getD_eq_getElem?_getD, hk']
    rw [List.take_succ, List.getElem?_eq_getElem hk']
    simp only [lastOpen, hg, Option.toList_some, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_eq_false_iff]
    by_cases ho : isOpen (l[k]'hk') = true
    · simp [ho]
    · have ho' : isOpen (l[k]'hk') = false := by simpa using ho
      simp only [ho', Bool.false_eq_true, _root_.ite_false, and_true]
      exact IH (by omega)

theorem lastOpen_length_none_iff (l : List Tok) : lastOpen l l.length = none ↔ l.any isOpen = false := by
  rw [lastOpen_none_iff l l.length (le_refl _), List.take_length]

/-- One `jsmn_parse` call from a fresh parser on an array of `ts.val.length` tokens: the model's
`parse` (the return value, and the first `min (max ret 0) n` tokens). -/
theorem jsmn_parse_spec (js : Slice U8) (ts : Slice JsmnTok) (hlen : js.val.length < 2 ^ 28) :
    ∃ v, jsmn_parse { pos := 0#usize, toknext := 0#usize, toksuper := (-1)#i32 } js ts = .ok v ∧
      (v.1.val, (v.2.2.val.take (min (max v.1.val 0).toNat ts.val.length)).map toTok) =
        parse (bytes js) ts.val.length := by
  have hc0 := hcast_i32_val (x := (0#usize : Usize)) (by simp)
  have hinv : Inv js { pos := 0#usize, toknext := 0#usize, toksuper := (-1)#i32 } ts
      (UScalar.hcast .I32 (0#usize : Usize)) := by
    refine ⟨hlen, by simp, by simp, by simp, by simp, by simp, ?_, by simp [hc0]⟩
    simp [mtoks]
  have habs0 : absSt { pos := 0#usize, toknext := 0#usize, toksuper := (-1)#i32 } ts = St.init := by
    simp [absSt, mtoks, St.init]
  obtain ⟨⟨p1, ts1, count1, ret1, stop1⟩, hl, hpost⟩ :=
    main_loop_eq js _ _ ts (UScalar.hcast .I32 (0#usize : Usize)) 0#i32 rfl hinv
  rw [habs0] at hpost
  unfold parse
  cases hm : mainLoop (bytes js) ts.val.length St.init with
  | error e =>
    rw [hm] at hpost
    obtain ⟨hstop, hret, he⟩ := hpost
    dsimp only at hstop hret
    subst hstop
    apply exists_ok_of_wp
    unfold jsmn_parse
    aeneas_wp [hl]
    refine ⟨_, rfl, ?_⟩
    simp only [hret, Prod.mk.injEq, true_and]
    rw [show (max e 0).toNat = 0 by omega]
    simp
  | ok st =>
    rw [hm] at hpost
    obtain ⟨hstop, habs, hinv1, hlen1⟩ := hpost
    dsimp only at hstop habs hinv1 hlen1
    subst hstop habs
    obtain ⟨-, hpos1, hk1, hkp1, hs11, hs21, hsz1, hcount1⟩ := hinv1
    have hck := hcast_i32_val (x := p1.toknext) (by omega)
    have hlo := lastOpen_length_none_iff (mtoks ts1 p1.toknext.val)
    rw [mtoks_length hk1] at hlo
    simp only [absSt]
    cases hl0 : lastOpen (mtoks ts1 p1.toknext.val) p1.toknext.val with
    | none =>
      have hany : (mtoks ts1 p1.toknext.val).any isOpen = false := hlo.1 hl0
      simp only [hany]
      apply exists_ok_of_wp
      unfold jsmn_parse
      aeneas_wp [hl, hck]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine find_open_wp ts1 p1.toknext.val hk1 p1.toknext.val (le_refl _) _
                  (by simp [hck]) ?_
      all_goals intro r hr
      all_goals rw [hl0] at hr
      all_goals simp only [optIdx] at hr
      all_goals aeneas_wp [hr, not_true_eq_false]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals simp only [Bool.false_eq_true, _root_.ite_false, mtoks_length hk1, hcount1,
        Prod.mk.injEq, true_and]
      all_goals rw [show (max (p1.toknext.val : Int) 0).toNat = p1.toknext.val by omega,
        Nat.min_eq_left (by omega)]
      all_goals rfl
    | some j =>
      have hany : (mtoks ts1 p1.toknext.val).any isOpen = true := by
        cases h : (mtoks ts1 p1.toknext.val).any isOpen
        · rw [hlo.2 h] at hl0
          cases hl0
        · rfl
      simp only [hany]
      apply exists_ok_of_wp
      unfold jsmn_parse
      aeneas_wp [hl, hck]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine find_open_wp ts1 p1.toknext.val hk1 p1.toknext.val (le_refl _) _
                  (by simp [hck]) ?_
      all_goals intro r hr
      all_goals rw [hl0] at hr
      all_goals simp only [optIdx] at hr
      all_goals aeneas_wp [hr, not_true_eq_false]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals simp [JSMN_ERROR_PART, ERROR_PART]

/-- **The Rust side**: for every input whose source is shorter than `2^28` bytes, the Rust run
returns (no panic, no divergence), and its observation is the model's `parse`. -/
theorem rust_spec (x : Input) (h : ¬ Long x) :
    ∃ y, rustRun x = .ok y ∧ rustObs x.2.val y = parse (bytes x.1) x.2.val := by
  have hlen : x.1.val.length < 2 ^ 28 := by
    unfold Long at h
    omega
  have hn : (initToks x.2).val.length = x.2.val := by
    simp [initToks]
  obtain ⟨⟨r, p', toks⟩, hj, hobs⟩ := jsmn_parse_spec x.1 (initToks x.2) hlen
  refine ⟨(r, toks), ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold rustRun jsmn_init
    aeneas_wp [hj]
  · rw [hn] at hobs
    exact hobs

end EquivLean.Demo.XLang.Jsmn.Rust
