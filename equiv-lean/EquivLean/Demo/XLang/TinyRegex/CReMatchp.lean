import EquivLean.Demo.XLang.TinyRegex.CMatchPat

/-!
# tiny-regex-c → model, C side: `re_matchp` (partial correctness)

`re_matchp_pspec`: `re_matchp(cp, text, matchlength)` for `re_compile`'s result `cp` (`cpPtr`):
every outcome returns the model's `reMatchp cp T` value, leaves its `matchlength` in
`*matchlength`, has no model UB, and changes no other block of the caller.  For the compiled regex
(`re_matchp_some_pspec`) `matchpattern`'s contract is a hypothesis, `hmp`, at pattern index 0 and
1 in the form `MPC` gives at a call memory; `re_matchp_pspec` takes it from `matchpattern_pspec`.
The search loop `do { idx += 1; … } while (*text++ != '\0');` runs in the hypothesis by an
invariant (`holds_do_inv`), the model's `searchLoop` behind its variables.  `re_matchp_null_pspec`:
the `NULL` pattern.
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

section model
open EquivLean.Demo.XLang.TinyRegex (Ctx mpLoop searchLoop reMatchp reMatch compile chk BEGIN)

section
variable (C : Ctx) (ti : Nat) (ml : Int)

/-- A match at `ti` (a byte of the text): `re_matchp` returns `idx = ti`. -/
theorem sl_match (ht : ti < C.T.size) (hc : C.T[ti] ≠ 0) (hch : chk ti = 0)
    (hok : (mpLoop C ml 0 ti ml 0).ok = true) :
    searchLoop C ti ml 0 = ((ti : Int), (mpLoop C ml 0 ti ml 0).ml, (mpLoop C ml 0 ti ml 0).ub) := by
  rw [searchLoop]; simp only [Nat.zero_or, hch]; simp [ht, hc, hok]

/-- No match at `ti` (a byte of the text): the search goes on at `ti + 1`. -/
theorem sl_next (ht : ti < C.T.size) (hc : C.T[ti] ≠ 0) (hch : chk ti = 0)
    (hok : (mpLoop C ml 0 ti ml 0).ok = false) (hu : (mpLoop C ml 0 ti ml 0).ub = 0) :
    searchLoop C ti ml 0 = searchLoop C (ti + 1) (mpLoop C ml 0 ti ml 0).ml 0 := by
  conv => lhs; rw [searchLoop]
  simp only [Nat.zero_or, hch]; simp [ht, hc, hok, hu]

/-- At the NUL: `-1`, whether `matchpattern` matched or not. -/
theorem sl_end (ht : ti = C.T.size) (hch : chk ti = 0) :
    searchLoop C ti ml 0 = (-1, (mpLoop C ml 0 ti ml 0).ml, (mpLoop C ml 0 ti ml 0).ub) := by
  rw [searchLoop]; simp only [Nat.zero_or, hch]; simp [ht]

end

theorem rmp_none (T : Array Nat) (ub : Nat) : reMatchp none T ub = (-1, 0, ub) := rfl

theorem rmp_begin (P : Array Tok) (B T : Array Nat) (hb : (P.getD 0 {}).type = BEGIN) :
    reMatchp (some (P, B)) T 0 =
      (if (mpLoop ⟨P, B, T⟩ 0 1 0 0 0).ok then 0 else -1, (mpLoop ⟨P, B, T⟩ 0 1 0 0 0).ml,
        (mpLoop ⟨P, B, T⟩ 0 1 0 0 0).ub) := by
  have h : ((P.getD 0 {}).type == BEGIN) = true := by simp only [hb, beq_self_eq_true]
  simp only [reMatchp, h, ↓reduceIte]

theorem rmp_search (P : Array Tok) (B T : Array Nat) (hb : (P.getD 0 {}).type ≠ BEGIN) :
    reMatchp (some (P, B)) T 0 = searchLoop ⟨P, B, T⟩ 0 0 0 := by
  have h : ((P.getD 0 {}).type == BEGIN) = false := by simpa using hb
  simp only [reMatchp, h, Bool.false_eq_true, ↓reduceIte]

end model

/-- The union `u` of a stored `regex_t`. -/
def tokU (t : Tok) : Val :=
  if t.type = 8 ∨ t.type = 9 then .agg [.undef, .ptr (.loc 24 [.idx t.ccl])] else .agg [.int t.ch, .undef]

theorem tokV_agg (t : Tok) : tokV 24 t = .agg [.int t.type, tokU t] := by
  unfold tokV tokU; split <;> rfl

theorem re_matchp_some_pspec (P : Array Tok) (B : Array Nat) (T : List Nat) (bt bl : Nat) (m : Mem)
    (kt kl kR : BlockKind) (tyt : Ty) (v0 : Val)
    (hR : m.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩)
    (hPs : P.size = 30) (hty : ∀ (i : Nat) (h : i < P.size), P[i].type < 256)
    (ht : m.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩)
    (htyt : ∃ es tlen, tyt = .array (.int es 8) tlen)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, v0⟩) (hkl : kl ≠ .readonly)
    (hn : 26 ≤ m.next) (hbt : bt < m.next) (hbl : bl < m.next) (hbtl : bt ≠ bl) (hbl26 : 26 ≤ bl)
    (hT : ∀ b ∈ T, 0 < b ∧ b < 256)
    (hmp : ∀ (pi ti : Nat) (ml : Int) (M : Mem), pi ≤ 1 → ti ≤ T.length →
      -2147483648 ≤ ml ∧ ml ≤ 2147483647 → M.blocks 25 = m.blocks 25 → M.blocks 24 = m.blocks 24 →
      M.blocks bt = m.blocks bt → M.blocks bl = some ⟨kl, true, .int true 32, .int ml⟩ → m.next ≤ M.next →
      pholds (evalCall ctx "matchpattern" [.ptr (.loc 25 [.idx pi]), .ptr (.loc bt [.idx ti]),
        .ptr (.loc bl [])] M)
        (MPost (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0) M bl kl)) :
    pholds (evalCall ctx "re_matchp" [.ptr (.loc 25 [.idx 0]), .ptr (.loc bt [.idx 0]), .ptr (.loc bl [])] m)
      (fun a => (EquivLean.Demo.XLang.TinyRegex.reMatchp (some (P, B)) T.toArray 0).2.2 = 0 ∧
        a.1 = .ret (some (.int (EquivLean.Demo.XLang.TinyRegex.reMatchp (some (P, B)) T.toArray 0).1)) ∧
        a.2.blocks bl = some ⟨kl, true, .int true 32,
          .int (EquivLean.Demo.XLang.TinyRegex.reMatchp (some (P, B)) T.toArray 0).2.1⟩ ∧
        (∀ b, b ≠ bl → b < m.next → a.2.blocks b = m.blocks b) ∧ m.next ≤ a.2.next) := by
  obtain ⟨es, tlen, cirH_tyt⟩ := htyt
  intro r hr
  have hs : (evalCall ctx "re_matchp" [.ptr (.loc 25 [.idx 0]), .ptr (.loc bt [.idx 0]),
      .ptr (.loc bl [])] m).holds (· = r) := by rw [hr]; rfl
  have cirH_ne : bt ≠ bl := hbtl
  have cirH_tok : ∀ t, tokV 24 t = .agg [.int t.type, tokU t] := tokV_agg
  have cirH_len : (P.toList.map (tokV 24)).length = 30 := by simp [hPs]
  have cirH_ty0 : P[0].type < 256 := hty 0 (by omega)
  have cirH_p0 : P.toList[0]? = some (P[0]'(by omega)) := by
    rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem (by omega)
  have cirH_tg : ∀ (i : Nat) (h : i < (patL T).length), (patL T)[i] = (patL T).getD i 0 :=
    fun i h => getElem_eq_getD h
  have cirH_plen : (patL T).length = T.length + 1 := patL_length T
  cir_hstep hs
  cir_hrun_c hs
  · -- not anchored: the search loop `do { idx += 1; … } while (*text++ != '\0');`
    obtain ⟨s0, hs0, hs⟩ := holds_do_name hs
    refine (fun hw => ?main) (holds_do_inv hs
      (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ s0.mem.next ≤ σ.mem.next ∧
        (∀ b, b ≠ m.next + 4 → b ≠ m.next + 2 → b ≠ bl → b < s0.mem.next →
          σ.mem.blocks b = s0.mem.blocks b) ∧
        ∃ (t : Nat) (mlc : Int),
          σ.mem.blocks (m.next + 4) = some ⟨.stack, true, .int true 32, .int ((t : Int) - 1)⟩ ∧
          σ.mem.blocks (m.next + 2) =
            some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bt [.idx t])⟩ ∧
          σ.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧ t ≤ T.length ∧
          (t : Int) ≤ 2147483648 ∧ (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
          EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ t mlc 0 =
            EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ 0 0 0)
      (fun a => (EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ 0 0 0).2.2 = 0 ∧
        a.2.mem.blocks bl = some ⟨kl, true, .int true 32,
          .int (EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ 0 0 0).2.1⟩ ∧
        (∀ b, b ≠ bl → b < m.next → a.2.mem.blocks b = m.blocks b) ∧ m.next ≤ a.2.mem.next ∧
        (a.1 = .exit (.ret (some (.int
            (EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ 0 0 0).1))) ∨
          (a.1 = .next ∧ (EquivLean.Demo.XLang.TinyRegex.searchLoop ⟨P, B, T.toArray⟩ 0 0 0).1 = -1 ∧
            a.2.env = s0.env ∧ a.2.names = s0.names ∧ s0.mem.next ≤ a.2.mem.next ∧
            (∀ b, b ≠ m.next + 4 → b ≠ m.next + 2 → b ≠ bl → b < s0.mem.next →
              a.2.mem.blocks b = s0.mem.blocks b))))
      ?init ?step)
    case init =>
      subst hs0
      refine ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ _ => rfl, 0, 0, ?_, ?_, ?_, Nat.zero_le _, by decide, by decide, rfl⟩
      · simp (disch := omega) only [upd_apply_same]; rfl
      · simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      · simp (disch := omega) only [upd_apply_ne, upd_apply_same]
    case step =>
      intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, t, mlc, cirH_idx, cirH_txt, cirH_bl, ht1, cirH_tr,
        cirH_mlr, hsl⟩ r2 hr2
      have hs2 := holds_of_eq_ok hr2
      have cirH_ct := (patL_char hT t).1
      have cirH_zt := (patL_char hT t).2
      have hT0 : ∀ (i : Nat) (h : i < T.toArray.size), T.toArray[i] ≠ 0 := fun i h => by
        have := (hT _ (List.getElem_mem (l := T) (by simpa using h))).1
        simp only [List.getElem_toArray]; omega
      subst hs0
      dsimp only at cirH_env cirH_names cirH_nx cirH_frame
      unfold doIter at hs2
      cir_hrun_c hs2
      -- `matchpattern(pattern, text, matchlength)` at `text = &T[t]`
      obtain ⟨⟨e3, m3⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2 (hmp 0 t mlc _ (by omega) ht1 cirH_mlr
        (by simp (disch := omega) only [upd_apply_ne, cirH_frame])
        (by simp (disch := omega) only [upd_apply_ne, cirH_frame])
        (by simp (disch := omega) only [upd_apply_ne, cirH_frame])
        (by simp (disch := omega) only [upd_apply_ne, cirH_bl])
        (by dsimp only; omega))
      obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
      dsimp only at cirH_f3 cirH_n3
      subst he3
      have hch : EquivLean.Demo.XLang.TinyRegex.chk (t : Int) = 0 := by
        unfold EquivLean.Demo.XLang.TinyRegex.chk
        split
        · rfl
        · rename_i h
          exfalso; apply h
          simp only [EquivLean.Demo.XLang.TinyRegex.INT_MIN, EquivLean.Demo.XLang.TinyRegex.INT_MAX]; omega
      cir_hrun_c hs2
      · -- no match, a byte of the text: `text++`, the loop continues at `t + 1`
        subst hs2
        have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc 0 t mlc 0).ok = false := by
          cases h : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc 0 t mlc 0).ok
          · rfl
          · rw [h] at cirA_br2; simp at cirA_br2
        have hlt : t < T.length := by omega
        refine ⟨rfl, rfl, by dsimp only at cirH_nx cirH_n3 ⊢; omega, ?_, t + 1,
          (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc 0 t mlc 0).ml, ?_, ?_, ?_, by omega,
          by omega, cirH_rg3, ?_⟩
        · intro b hb1 hb2 hb3 hb4
          dsimp only at hb4
          simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_f3, cirH_frame b hb1 hb2 hb3 hb4]
        · rw [show ((t + 1 : Nat) : Int) - 1 = (t : Int) by omega]
          simp (disch := omega) only [killRange_of_lt, upd_apply_ne, upd_apply_same, cirH_f3]
        · simp (disch := omega) only [upd_apply_same]
        · simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_m3]
        · rw [← hsl]
          exact (sl_next _ _ _ (by simpa using hlt) (hT0 t _) hch hok
            cirH_u3).symm
      · -- no match at the NUL: the loop ends
        subst hs2
        have hte : t = T.length := by omega
        have hsl' := hsl
        rw [sl_end _ _ _ (by simpa using hte) hch] at hsl'
        rw [← hsl']
        refine ⟨cirH_u3, ?_, ?_, by dsimp only at cirH_nx cirH_n3 ⊢; omega,
          Or.inr ⟨rfl, rfl, rfl, rfl, by dsimp only at cirH_nx cirH_n3 ⊢; omega, ?_⟩⟩
        · simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_m3]
        · intro b hb1 hb2
          simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_f3,
            cirH_frame b (by omega) (by omega) hb1 (by omega)]
        · intro b hb1 hb2 hb3 hb4
          dsimp only at hb4
          simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_f3, cirH_frame b hb1 hb2 hb3 hb4]
      · -- a match at a byte of the text: `return idx`
        subst hs2
        have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc 0 t mlc 0).ok = true := by
          cases h : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc 0 t mlc 0).ok
          · rw [h] at cirH_br2; simp at cirH_br2
          · rfl
        have hlt : t < T.length := by omega
        have hsl' := hsl
        rw [sl_match _ _ _ (by simpa using hlt) (hT0 t _) hch hok] at hsl'
        rw [← hsl']
        refine ⟨cirH_u3, ?_, ?_, by dsimp only [Mem.endScope] at cirH_nx cirH_n3 ⊢; omega, Or.inl rfl⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3]
        · intro b hb1 hb2
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3,
            cirH_frame b (by omega) (by omega) hb1 (by omega)]
      · -- a match at the NUL: `return -1`
        subst hs2
        have hte : t = T.length := by omega
        have hsl' := hsl
        rw [sl_end _ _ _ (by simpa using hte) hch] at hsl'
        rw [← hsl']
        refine ⟨cirH_u3, ?_, ?_, by dsimp only [Mem.endScope] at cirH_nx cirH_n3 ⊢; omega, Or.inl rfl⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3]
        · intro b hb1 hb2
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3,
            cirH_frame b (by omega) (by omega) hb1 (by omega)]
    case main =>
      obtain ⟨⟨st1, σ1⟩, ⟨hub1, hbl1, hfrm1, hnxm1, hcase⟩, hk1⟩ := hw
      have hb : (P.getD 0 {}).type ≠ EquivLean.Demo.XLang.TinyRegex.BEGIN := by
        have h0 : P.getD 0 {} = P[0]'(by omega) := by simp [Array.getD, hPs]
        rw [h0]; simp only [EquivLean.Demo.XLang.TinyRegex.BEGIN]; omega
      rw [rmp_search P B _ hb]
      rcases hcase with hst1 | ⟨hst1, hres1, henv1, hnames1, hnx1, hfr1⟩
      · dsimp only at hst1 hbl1 hfrm1 hnxm1
        subst hst1
        clear hs
        cir_hrun_c hk1
        subst hk1
        refine ⟨hub1, rfl, ?_, ?_, ?_⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, hbl1]
        · intro b hb1 hb2
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, hfrm1 b hb1 hb2]
        · simp only [Mem.endScope]; omega
      · dsimp only at hst1 hbl1 hfrm1 hnxm1 henv1 hnames1 hnx1 hfr1
        subst hst1
        clear hs
        subst hs0
        cir_hrun_c hk1
        subst hk1
        refine ⟨hub1, by rw [hres1], ?_, ?_, ?_⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, hbl1]
        · intro b hb1 hb2
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, hfrm1 b hb1 hb2]
        · simp only [Mem.endScope]; omega
  · -- anchored (`^`): `matchpattern(&pattern[1], text, matchlength)`
    obtain ⟨⟨e1, m1⟩, -, hp1, hs⟩ := holds_pspec_elim hs (hmp 1 0 0 _ (by omega) (by omega) (by decide)
      (by simp (disch := omega) only [upd_apply_ne])
      (by simp (disch := omega) only [upd_apply_ne])
      (by simp (disch := omega) only [upd_apply_ne])
      (by simp (disch := omega) only [upd_apply_same])
      (by dsimp only; omega))
    obtain ⟨cirH_u1, he1, cirH_rg1, cirH_m1, cirH_f1, cirH_n1⟩ := hp1
    dsimp only at cirH_f1 cirH_n1
    subst he1
    cir_hrun_c hs
    subst hs
    have hb : (P.getD 0 {}).type = EquivLean.Demo.XLang.TinyRegex.BEGIN := by
      have h0 : P.getD 0 {} = P[0]'(by omega) := by simp [Array.getD, hPs]
      rw [h0]; simp only [EquivLean.Demo.XLang.TinyRegex.BEGIN]; omega
    rw [rmp_begin P B _ hb]
    refine ⟨cirH_u1, ?_, ?_, ?_, ?_⟩
    · cases hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ 0 1 0 0 0).ok <;> simp
    · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m1]
    · intro b hb1 hb2
      simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1]
    · simp only [Mem.endScope]; omega


/-- `re_matchp(NULL, text, matchlength)`: `-1`, and `*matchlength = 0`. -/
theorem re_matchp_null_pspec (T : List Nat) (bt bl : Nat) (m : Mem) (kl : BlockKind) (v0 : Val)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, v0⟩) (hkl : kl ≠ .readonly) (hbl : bl < m.next) :
    pholds (evalCall ctx "re_matchp" [.ptr .null, .ptr (.loc bt [.idx 0]), .ptr (.loc bl [])] m)
      (fun a => (EquivLean.Demo.XLang.TinyRegex.reMatchp none T.toArray 0).2.2 = 0 ∧
        a.1 = .ret (some (.int (EquivLean.Demo.XLang.TinyRegex.reMatchp none T.toArray 0).1)) ∧
        a.2.blocks bl = some ⟨kl, true, .int true 32,
          .int (EquivLean.Demo.XLang.TinyRegex.reMatchp none T.toArray 0).2.1⟩ ∧
        (∀ b, b ≠ bl → b < m.next → a.2.blocks b = m.blocks b) ∧ m.next ≤ a.2.next) := by
  intro r hr
  have hs : (evalCall ctx "re_matchp" [.ptr .null, .ptr (.loc bt [.idx 0]), .ptr (.loc bl [])] m).holds
      (· = r) := by rw [hr]; rfl
  cir_hstep hs
  cir_hrun_c hs
  subst hs
  rw [rmp_none]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
  · intro b hb1 hb2
    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
  · simp only [Mem.endScope]; omega

/-- `re_compile`'s result as `re_matchp`'s first argument: `NULL`, or `&re_compiled[0]`. -/
def cpPtr : Option (Array Tok × Array Nat) → Val
  | none => .ptr .null
  | some _ => .ptr (.loc 25 [.idx 0])

/-- `re_matchp(cp, text, matchlength)` for `re_compile`'s result `cp` (the composition's
statement): `matchpattern`'s contract comes from `matchpattern_pspec`. -/
theorem re_matchp_pspec (cp : Option (Array Tok × Array Nat)) (T : List Nat) (bt bl : Nat) (m : Mem)
    (kt kl : BlockKind) (tyt : Ty) (vl : Val)
    (hcp : ∀ P B, cp = some (P, B) → ∃ kR kC,
      m.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩ ∧
      m.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
        .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩ ∧
      P.size = 30 ∧ (∀ x ∈ B.toList, x < 256) ∧ (∀ (i : Nat) (hi : i < P.size), TokOK B P[i]))
    (ht : m.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩)
    (htyt : ∃ es tlen, tyt = .array (.int es 8) tlen)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, vl⟩) (hkl : kl ≠ .readonly)
    (hn : 26 ≤ m.next) (hbt : bt < m.next) (hbl : bl < m.next) (hbtl : bt ≠ bl) (hbt26 : 26 ≤ bt)
    (hbl26 : 26 ≤ bl) (hT : ∀ b ∈ T, 0 < b ∧ b < 256) :
    pholds (evalCall ctx "re_matchp" [cpPtr cp, .ptr (.loc bt [.idx 0]), .ptr (.loc bl [])] m)
      (fun r => (EquivLean.Demo.XLang.TinyRegex.reMatchp cp T.toArray 0).2.2 = 0 ∧
        r.1 = .ret (some (.int (EquivLean.Demo.XLang.TinyRegex.reMatchp cp T.toArray 0).1)) ∧
        r.2.blocks bl = some ⟨kl, true, .int true 32,
          .int (EquivLean.Demo.XLang.TinyRegex.reMatchp cp T.toArray 0).2.1⟩ ∧
        (∀ b, b ≠ bl → b < m.next → r.2.blocks b = m.blocks b) ∧ m.next ≤ r.2.next) := by
  rcases cp with _ | ⟨P, B⟩
  · exact re_matchp_null_pspec T bt bl m kl vl hl hkl hbl
  · obtain ⟨kR, kC, hR, hC, hPs, hB, hP⟩ := hcp P B rfl
    refine re_matchp_some_pspec P B T bt bl m kt kl kR tyt vl hR hPs (fun i hi => (hP i hi).1) ht htyt hl hkl
      hn hbt hbl hbtl hbl26 hT ?_
    intro pi ti ml M hpi hti hml h25 h24 hbt' hbl' hnx
    exact matchpattern_pspec P B hPs hB hP pi (by omega) T ti bt bl ml M kt kl kR kC tyt (h25.trans hR)
      (h24.trans hC) (hbt'.trans ht) htyt hbl' hkl (by omega) (by omega) (by omega) hbtl hbt26 hbl26 hT hti hml

end EquivLean.Demo.XLang.TinyRegex.C
