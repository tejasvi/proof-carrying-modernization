import EquivLean.Demo.XLang.TinyRegex.CMatchP

/-!
# tiny-regex-c → model, C side: `matchpattern` (partial correctness)

`MPC P B pi` is the contract of `matchpattern(&re_compiled[pi], text, matchlength)`.  Its `do`-`while`
loop runs in the hypothesis (`holds_do_inv`); the calls of `matchquestion`, `matchstar` and
`matchplus` at `&pattern[2]` use their contracts with `MPC` at the larger pattern index as the
induction hypothesis.
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.XLang.TinyRegex.C

/-! ### The model's `mpLoop`, by path -/

section
open EquivLean.Demo.XLang.TinyRegex (Ctx mpLoop matchquestion matchstar matchplus matchone rd chk UNUSED
  QUESTIONMARK STAR PLUS END)
variable (C : Ctx) (pre : Int) (p t : Nat) (ml : Int)

theorem mp_unused (hp : p < C.P.size) (h0 : C.P[p].type = 0) (h2 : p + 2 ≤ C.P.size) :
    mpLoop C pre p t ml 0 = matchquestion C C.P[p] (p + 2) t ml 0 := by
  rw [mpLoop]; simp [hp, UNUSED, h0, h2]

theorem mp_q (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h1 : C.P[p + 1].type = 4) :
    mpLoop C pre p t ml 0 = matchquestion C C.P[p] (p + 2) t ml 0 := by
  rw [mpLoop]; simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, h0, h1]

theorem mp_star (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h1 : C.P[p + 1].type = 5) :
    mpLoop C pre p t ml 0 = matchstar C C.P[p] (p + 2) t ml 0 := by
  rw [mpLoop]; simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, h0, h1]

theorem mp_plus (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h1 : C.P[p + 1].type = 6) :
    mpLoop C pre p t ml 0 = matchplus C C.P[p] (p + 2) t ml 0 := by
  rw [mpLoop]; simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, h0, h1]

theorem mp_end_eq (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type = 3) (h1 : C.P[p + 1].type = 0)
    (ht : t = C.T.size) : mpLoop C pre p t ml 0 = ⟨true, ml, 0⟩ := by
  have hr : rd C.T t = (0, 0) := by unfold rd; rw [dite_eq_right (by omega), ite_eq_left ht]
  rw [mpLoop]; simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, END, h0, h1, hr]

theorem mp_end_lt (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type = 3) (h1 : C.P[p + 1].type = 0)
    (ht : t < C.T.size) (hc : C.T[t] ≠ 0) : mpLoop C pre p t ml 0 = ⟨false, ml, 0⟩ := by
  have hr : rd C.T t = (C.T[t], 0) := by simp [rd, ht]
  rw [mpLoop]; simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, END, h0, h1, hr, hc]

theorem mp_step (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h4 : C.P[p + 1].type ≠ 4)
    (h5 : C.P[p + 1].type ≠ 5) (h6 : C.P[p + 1].type ≠ 6) (h3 : ¬ (C.P[p].type = 3 ∧ C.P[p + 1].type = 0))
    (ht : t < C.T.size) (hc : C.T[t] ≠ 0) (hm : (matchone C C.P[p] C.T[t]).1 = true)
    (hmu : (matchone C C.P[p] C.T[t]).2 = 0) (hov : -2147483648 ≤ ml + 1 ∧ ml + 1 ≤ 2147483647) :
    mpLoop C pre p t ml 0 = mpLoop C pre (p + 1) (t + 1) (ml + 1) 0 := by
  have hr : rd C.T t = (C.T[t], 0) := by simp [rd, ht]
  have hch : chk (ml + 1) = 0 := by
    simp only [chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN, EquivLean.Demo.XLang.TinyRegex.INT_MAX, hov,
      and_self, ite_true]
  conv => lhs; rw [mpLoop]
  simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, END, h0, h4, h5, h6, hr, hc, hch,
    hmu, hm, h3]

theorem mp_nomatch (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h4 : C.P[p + 1].type ≠ 4)
    (h5 : C.P[p + 1].type ≠ 5) (h6 : C.P[p + 1].type ≠ 6) (h3 : ¬ (C.P[p].type = 3 ∧ C.P[p + 1].type = 0))
    (ht : t < C.T.size) (hc : C.T[t] ≠ 0) (hm : (matchone C C.P[p] C.T[t]).1 = false)
    (hmu : (matchone C C.P[p] C.T[t]).2 = 0) (hov : -2147483648 ≤ ml + 1 ∧ ml + 1 ≤ 2147483647) :
    mpLoop C pre p t ml 0 = ⟨false, pre, 0⟩ := by
  have hr : rd C.T t = (C.T[t], 0) := by simp [rd, ht]
  have hch : chk (ml + 1) = 0 := by
    simp only [chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN, EquivLean.Demo.XLang.TinyRegex.INT_MAX, hov,
      and_self, ite_true]
  rw [mpLoop]
  simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, END, h0, h4, h5, h6, hr, hc, hch,
    hmu, hm, h3]

theorem mp_textend (hp1 : p + 1 < C.P.size) (h0 : C.P[p].type ≠ 0) (h4 : C.P[p + 1].type ≠ 4)
    (h5 : C.P[p + 1].type ≠ 5) (h6 : C.P[p + 1].type ≠ 6) (h3 : ¬ (C.P[p].type = 3 ∧ C.P[p + 1].type = 0))
    (ht : t = C.T.size) (hov : -2147483648 ≤ ml + 1 ∧ ml + 1 ≤ 2147483647) :
    mpLoop C pre p t ml 0 = ⟨false, pre, 0⟩ := by
  have hr : rd C.T t = (0, 0) := by unfold rd; rw [dite_eq_right (by omega), ite_eq_left ht]
  have hch : chk (ml + 1) = 0 := by
    simp only [chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN, EquivLean.Demo.XLang.TinyRegex.INT_MAX, hov,
      and_self, ite_true]
  rw [mpLoop]
  simp [show p < C.P.size by omega, hp1, UNUSED, QUESTIONMARK, STAR, PLUS, END, h0, h4, h5, h6, hr, hch, h3]

end

/-- The contract of `matchpattern(&re_compiled[pi], &T[ti], matchlength)` against the model's
`mpLoop`, for the compiled regex `P` (block 25) and its class buffer `B` (block 24). -/
def MPC (P : Array Tok) (B : Array Nat) (pi : Nat) : Prop :=
  ∀ (T : List Nat) (ti bt bl : Nat) (ml : Int) (m : Mem) (kt kl kR kC : BlockKind) (tyt : Ty),
    m.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩ →
    m.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
      .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩ →
    m.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩ → (∃ es tlen, tyt = .array (.int es 8) tlen) →
    m.blocks bl = some ⟨kl, true, .int true 32, .int ml⟩ → kl ≠ .readonly →
    26 ≤ m.next → bt < m.next → bl < m.next → bt ≠ bl → 26 ≤ bt → 26 ≤ bl →
    (∀ b ∈ T, 0 < b ∧ b < 256) → ti ≤ T.length → (-2147483648 ≤ ml ∧ ml ≤ 2147483647) →
    pholds (evalCall ctx "matchpattern" [.ptr (.loc 25 [.idx pi]), .ptr (.loc bt [.idx ti]),
      .ptr (.loc bl [])] m)
      (MPost (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0) m bl kl)

/-- `MPC` at `p` gives the induction hypothesis of the matcher contracts at a call memory `M`. -/
theorem ihmp_of_MPC {P : Array Tok} {B : Array Nat} {p : Nat} {T : List Nat} {bt bl : Nat}
    {kt kl kR kC : BlockKind} {tyt : Ty} {M : Mem} (h : MPC P B p)
    (hR : M.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩)
    (hC : M.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
      .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩)
    (ht : M.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩)
    (htyt : ∃ es tlen, tyt = .array (.int es 8) tlen) (hkl : kl ≠ .readonly)
    (hn : 26 ≤ M.next) (hbt : bt < M.next) (hbl : bl < M.next) (hbtl : bt ≠ bl) (hbt26 : 26 ≤ bt)
    (hbl26 : 26 ≤ bl) (hT : ∀ b ∈ T, 0 < b ∧ b < 256) :
    ∀ (t' : Nat) (ml' : Int) (m' : Mem), t' ≤ T.length → -2147483648 ≤ ml' ∧ ml' ≤ 2147483647 →
      m'.blocks bl = some ⟨kl, true, .int true 32, .int ml'⟩ → m'.blocks 25 = M.blocks 25 →
      m'.blocks 24 = M.blocks 24 → m'.blocks bt = M.blocks bt → M.next ≤ m'.next →
      pholds (evalCall ctx "matchpattern" [.ptr (.loc 25 [.idx p]), .ptr (.loc bt [.idx t']),
        .ptr (.loc bl [])] m')
        (MPost (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml' p t' ml' 0) m' bl kl) :=
  fun t' ml' m' h1 h2 h3 h4 h5 h6 h7 =>
    h T t' bt bl ml' m' kt kl kR kC tyt (h4.trans hR) (h5.trans hC) (h6.trans ht) htyt h3 hkl (by omega)
      (by omega) (by omega) hbtl hbt26 hbl26 hT h1 h2

/-- `matchpattern` at `pi`, given the contract at every larger pattern index. -/
theorem matchpattern_step (P : Array Tok) (B : Array Nat) (pi : Nat) (hPs : P.size = 30)
    (hB : ∀ x ∈ B.toList, x < 256) (hP : ∀ (i : Nat) (hi : i < P.size), TokOK B P[i])
    (hpi : pi ≤ 30) (IH : ∀ p', pi < p' → p' ≤ 30 → MPC P B p') : MPC P B pi := by
  intro T ti bt bl ml m kt kl kR kC tyt hR hC ht htyt hl hkl hn hbt hbl hbtl hbt26 hbl26 hT hti hml r hr
  have htyt0 := htyt
  obtain ⟨es, tlen, cirH_tyt⟩ := htyt0
  have hs := holds_of_eq_ok hr
  have cirH_t0 : ∀ n : Nat, ((n : Int) + 0).toNat = n := fun n => by omega
  have cirH_t1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  have cirH_t2 : ∀ n : Nat, ((n : Int) + 2).toNat = n + 2 := fun n => by omega
  have cirH_tg : ∀ (i : Nat) (h : i < (patL T).length), (patL T)[i] = (patL T).getD i 0 :=
    fun i h => getElem_eq_getD h
  have cirH_len : (patL T).length = T.length + 1 := patL_length T
  have cirH_ne : bt ≠ bl := hbtl
  have cirH_tv0 : ∀ t : Tok, (tokV 24 t).get? [.idx 0] = some (.int t.type) := fun t => by
    unfold tokV; split <;> rfl
  have cirH_Plen : (P.toList.map (tokV 24)).length = 30 := by simp [hPs]
  have cirH_Pg : ∀ (i : Nat) (h : i < (P.toList.map (tokV 24)).length),
      (P.toList.map (tokV 24))[i] = tokV 24 P[i]! := by
    intro i h
    rw [List.getElem_map, Array.getElem_toList, getElem!_pos P i (by simpa using h)]
  have hPty : ∀ i : Nat, P[i]!.type < 256 := by
    intro i
    by_cases h : i < P.size
    · rw [getElem!_pos P i h]; exact (hP i h).1
    · rw [getElem!_neg P i h]; show (0 : Nat) < 256; decide
  cir_hstep hs
  cir_hrun_c hs
  obtain ⟨s0, hs0, hs⟩ := holds_do_name hs
  refine (fun hw => ?main) (holds_do_inv hs
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ s0.mem.next ≤ σ.mem.next ∧
      (∀ b, b ≠ m.next + 1 → b ≠ m.next + 2 → b ≠ bl → b < s0.mem.next → σ.mem.blocks b = s0.mem.blocks b) ∧
      ∃ (p t : Nat) (mlc : Int),
        σ.mem.blocks (m.next + 1) = some ⟨.stack, true, (Ty.record "regex_t").ptr, .ptr (.loc 25 [.idx p])⟩ ∧
        σ.mem.blocks (m.next + 2) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bt [.idx t])⟩ ∧
        σ.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧
        pi ≤ p ∧ p ≤ 30 ∧ t ≤ T.length ∧ (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
        EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml p t mlc 0 =
          EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0)
    (fun a => s0.mem.next ≤ a.2.mem.next ∧
      ((∃ v, a.1 = .exit (.ret (some (.int v))) ∧
          MPost (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0) m bl kl
            (.ret (some (.int v)), a.2.mem)) ∨
       (a.1 = .next ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧
          EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0 = ⟨false, ml, 0⟩ ∧
          (∀ b, b ≠ m.next + 1 → b ≠ m.next + 2 → b ≠ bl → b < s0.mem.next →
            a.2.mem.blocks b = s0.mem.blocks b) ∧
          ∃ mlc : Int, a.2.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩)))
    ?init ?step)
  case init =>
    subst hs0
    refine ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ _ => rfl, pi, ti, ml, ?_, ?_, ?_, Nat.le_refl _, hpi, hti, hml, rfl⟩
    · simp (disch := omega) only [upd_apply_ne, upd_apply_same]
    · simp (disch := omega) only [upd_apply_ne, upd_apply_same]
    · simp (disch := omega) only [upd_apply_ne, hl]
  case step =>
    intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, p, t, mlc, cirH_sp, cirH_st, cirH_bl, hp1, hp2, ht2,
      cirH_mlr, hmod⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    have cirH_ct := (patL_char hT t).1
    have cirH_zt := (patL_char hT t).2
    subst hs0
    dsimp only at cirH_env cirH_names cirH_nx cirH_frame
    have cirH_b25 : σ.mem.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩ := by
      rw [cirH_frame 25 (by omega) (by omega) (by omega) (by omega)]; simp (disch := omega) only [upd_apply_ne, hR]
    have cirH_bt : σ.mem.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩ := by
      rw [cirH_frame bt (by omega) (by omega) (by omega) (by omega)]; simp (disch := omega) only [upd_apply_ne, ht]
    have cirH_b24 : σ.mem.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
        .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩ := by
      rw [cirH_frame 24 (by omega) (by omega) (by omega) (by omega)]; simp (disch := omega) only [upd_apply_ne, hC]
    have cirH_ty0 : ((P[p]!.type : Nat) : Int) ≤ 255 := by have := hPty p; omega
    have cirH_ty1 : ((P[p + 1]!.type : Nat) : Int) ≤ 255 := by have := hPty (p + 1); omega
    unfold doIter at hs2
    rcases Nat.lt_or_ge p 30 with hp30 | hp30
    · rcases Nat.lt_or_ge (p + 1) 30 with hp29 | hp29
      · have cirH_Pp0 : P.toList[p]? = some P[p]! := by
          rw [Array.getElem?_toList, getElem!_pos P p (by omega)]; exact getElem?_pos P p (by omega)
        have cirH_Pp1 : P.toList[p + 1]? = some P[p + 1]! := by
          rw [Array.getElem?_toList, getElem!_pos P (p + 1) (by omega)]; exact getElem?_pos P (p + 1) (by omega)
        have hPp : P[p]! = P[p] := getElem!_pos P p (by omega)
        have hPp1 : P[p + 1]! = P[p + 1] := getElem!_pos P (p + 1) (by omega)
        have hTokp : TokOK B P[p]! := by rw [hPp]; exact hP p (by omega)
        have hPs' : (⟨P, B, T.toArray⟩ : EquivLean.Demo.XLang.TinyRegex.Ctx).P.size = 30 := hPs
        have hTs : (⟨P, B, T.toArray⟩ : EquivLean.Demo.XLang.TinyRegex.Ctx).T.size = T.length := by simp
        cir_hrun_c hs2
        all_goals (try subst hs2)
        all_goals first
          | -- the end of the text: the loop ends
            have hte : t = T.length := by omega
            have hmodel : EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0 = ⟨false, ml, 0⟩ := by
              rw [← hmod]
              exact mp_textend _ _ _ _ _ (by omega) (by rw [← hPp]; omega) (by rw [← hPp1]; omega)
                (by rw [← hPp1]; omega) (by rw [← hPp1]; omega) (by rw [← hPp, ← hPp1]; omega) (by omega) (by omega)
            exact ⟨by dsimp only [Mem.endScope]; omega, Or.inr ⟨rfl, rfl, rfl, hmodel,
              fun b hb1 hb2 hb3 hb4 => by
                dsimp only at hb4
                simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_frame b hb1 hb2 hb3 hb4],
              mlc + 1, by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same]⟩⟩
          | -- `END` followed by `UNUSED`: `return (text[0] == '\0')`
            have hmodel : EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0 =
                ⟨decide (T.length ≤ t), mlc, 0⟩ := by
              rw [← hmod]
              by_cases hte : T.length ≤ t
              · rw [mp_end_eq _ _ _ _ _ (by omega) (by rw [← hPp]; omega) (by rw [← hPp1]; omega) (by omega)]
                simp [hte]
              · have hlt : t < T.length := by omega
                have hb0 : T.toArray[t] ≠ 0 := by have := (hT _ (by simp : T.toArray[t] ∈ T)).1; omega
                rw [mp_end_lt _ _ _ _ _ (by omega) (by rw [← hPp]; omega) (by rw [← hPp1]; omega) (by simpa using hlt)
                  hb0]
                simp [hte]
            refine ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, ?_⟩⟩
            rw [hmodel]
            exact ⟨rfl, by by_cases hte : T.length ≤ t <;> simp [hte], cirH_mlr,
              by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_bl],
              fun b hb1 hb2 => by
                simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne,
                  cirH_frame b (by omega) (by omega) hb1 (by omega)],
              by dsimp only [Mem.endScope]; omega⟩
          | -- `matchone(*pattern++, *text++)`
            have hlt : t < T.length := by omega
            have hbyte : (patL T).getD t 0 = sc T.toArray[t] := by
              rw [patL_getD_lt hlt]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            have hb256 : T.toArray[t] < 256 := (hT _ (by simp)).2
            have hb0 : T.toArray[t] ≠ 0 := by have := (hT _ (by simp : T.toArray[t] ∈ T)).1; omega
            have hov : -2147483648 ≤ mlc + 1 ∧ mlc + 1 ≤ 2147483647 := by omega
            obtain ⟨⟨e2, m7⟩, -, ⟨hmu, w2, cirH_v2, cirH_r2a, cirH_r2b, cirH_r2c, cirH_fr2b, cirH_fr2a⟩, hs2⟩ :=
              holds_pspec_elim hs2 (matchone_pspec ⟨P, B, T.toArray⟩ P[p]! T.toArray[t] _ kC _
                (by simp (disch := omega) only [upd_apply_ne, cirH_b24]) (by dsimp only; omega) hB hTokp
                (by omega) hb256 hbyte)
            dsimp only at cirH_v2 cirH_fr2a cirH_fr2b
            subst cirH_v2
            rw [hPp] at hmu cirH_r2c
            by_cases hw2 : w2 = 0
            · -- no match: the loop ends
              subst hw2
              have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ P[p] T.toArray[t]).1 = false := by
                cases hh : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ P[p] T.toArray[t]).1
                · rfl
                · exact absurd (cirH_r2c.2 hh) (by omega)
              have hmodel : EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0 = ⟨false, ml, 0⟩ := by
                rw [← hmod]
                exact mp_nomatch _ _ _ _ _ (by omega) (by rw [← hPp]; omega) (by rw [← hPp1]; omega)
                  (by rw [← hPp1]; omega) (by rw [← hPp1]; omega) (by rw [← hPp, ← hPp1]; omega) (by simpa using hlt)
                  hb0 hm hmu hov
              cir_hrun_c hs2
              subst hs2
              exact ⟨by dsimp only [Mem.endScope] at *; omega, Or.inr ⟨rfl, rfl, rfl, hmodel,
                fun b hb1 hb2 hb3 hb4 => by
                  dsimp only at hb4
                  simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b,
                    cirH_frame b hb1 hb2 hb3 hb4],
                mlc + 1, by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b,
                  upd_apply_same]⟩⟩
            · -- a match: the loop goes on at `p + 1`, `t + 1`
              have cirH_w2t : (w2 != 0) = true := by simpa using hw2
              have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ P[p] T.toArray[t]).1 = true :=
                cirH_r2c.1 hw2
              cir_hrun_c hs2
              subst hs2
              refine ⟨rfl, rfl, by dsimp only [Mem.endScope] at *; omega,
                fun b hb1 hb2 hb3 hb4 => by
                  dsimp only at hb4
                  simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b,
                    cirH_frame b hb1 hb2 hb3 hb4],
                p + 1, t + 1, mlc + 1,
                by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, upd_apply_same],
                by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, upd_apply_same],
                by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, upd_apply_same],
                by omega, by omega, by omega, hov, ?_⟩
              rw [← hmod]
              exact (mp_step _ _ _ _ _ (by omega) (by rw [← hPp]; omega) (by rw [← hPp1]; omega)
                (by rw [← hPp1]; omega) (by rw [← hPp1]; omega) (by rw [← hPp, ← hPp1]; omega) (by simpa using hlt)
                hb0 hm hmu hov).symm
          | skip
        -- `matchquestion`, `matchstar` or `matchplus` at `&pattern[2]`
        all_goals
          have IHmp := ihmp_of_MPC (IH (p + 2) (by omega) (by omega)) cirH_b25 cirH_b24 cirH_bt htyt hkl (by omega)
            (by omega) (by omega) hbtl hbt26 hbl26 hT
          by_cases hq0 : P[p]!.type = 0
          · -- `UNUSED`
            first
              | (exfalso; omega)
              | obtain ⟨⟨e3, m3⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2
                  (matchquestion_pspec P B T P[p]! (p + 2) t bt bl mlc _ kt kl kR kC tyt cirH_b25 cirH_b24 cirH_bt htyt cirH_bl hkl
                    (by first | omega | (dsimp only; omega)) (by first | omega | (dsimp only; omega))
                    (by first | omega | (dsimp only; omega)) hbtl hbt26 hbl26 hB hTokp hT ht2 cirH_mlr IHmp)
                obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
                try dsimp only at cirH_f3 cirH_n3
                subst he3
                cir_hrun_c hs2
                subst hs2
                refine ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, ?_⟩⟩
                rw [← hmod, mp_unused _ _ _ _ _ (by omega) (by rw [← hPp]; exact hq0) (by omega), ← hPp]
                exact ⟨cirH_u3, rfl, cirH_rg3,
                  by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3],
                  fun b hb1 hb2 => by
                    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3 b hb1 (by omega),
                      cirH_frame b (by omega) (by omega) hb1 (by omega)],
                  by dsimp only [Mem.endScope]; omega⟩
          · by_cases hq4 : P[p + 1]!.type = 4
            · -- `?`
              first
                | (exfalso; omega)
                | obtain ⟨⟨e3, m3⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2
                    (matchquestion_pspec P B T P[p]! (p + 2) t bt bl mlc _ kt kl kR kC tyt cirH_b25 cirH_b24 cirH_bt htyt cirH_bl hkl
                      (by first | omega | (dsimp only; omega)) (by first | omega | (dsimp only; omega))
                      (by first | omega | (dsimp only; omega)) hbtl hbt26 hbl26 hB hTokp hT ht2 cirH_mlr IHmp)
                  obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
                  try dsimp only at cirH_f3 cirH_n3
                  subst he3
                  cir_hrun_c hs2
                  subst hs2
                  refine ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, ?_⟩⟩
                  rw [← hmod, mp_q _ _ _ _ _ (by omega) (by rw [← hPp]; exact hq0) (by rw [← hPp1]; exact hq4), ← hPp]
                  exact ⟨cirH_u3, rfl, cirH_rg3,
                    by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3],
                    fun b hb1 hb2 => by
                      simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3 b hb1 (by omega),
                        cirH_frame b (by omega) (by omega) hb1 (by omega)],
                    by dsimp only [Mem.endScope]; omega⟩
            · by_cases hq5 : P[p + 1]!.type = 5
              · -- `*`
                first
                  | (exfalso; omega)
                  | obtain ⟨⟨e3, m3⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2
                      (matchstar_pspec P B T P[p]! (p + 2) t bt bl mlc _ kt kl kR kC tyt cirH_b25 cirH_b24 cirH_bt htyt cirH_bl hkl
                        (by first | omega | (dsimp only; omega)) (by first | omega | (dsimp only; omega))
                        (by first | omega | (dsimp only; omega)) hbtl hbt26 hbl26 hB hTokp hT ht2 cirH_mlr IHmp)
                    obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
                    try dsimp only at cirH_f3 cirH_n3
                    subst he3
                    cir_hrun_c hs2
                    subst hs2
                    refine ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, ?_⟩⟩
                    rw [← hmod, mp_star _ _ _ _ _ (by omega) (by rw [← hPp]; exact hq0) (by rw [← hPp1]; exact hq5), ← hPp]
                    exact ⟨cirH_u3, rfl, cirH_rg3,
                      by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3],
                      fun b hb1 hb2 => by
                        simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3 b hb1 (by omega),
                          cirH_frame b (by omega) (by omega) hb1 (by omega)],
                      by dsimp only [Mem.endScope]; omega⟩
              · -- `+`
                first
                  | (exfalso; omega)
                  | obtain ⟨⟨e3, m3⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2
                      (matchplus_pspec P B T P[p]! (p + 2) t bt bl mlc _ kt kl kR kC tyt cirH_b25 cirH_b24 cirH_bt htyt cirH_bl hkl
                        (by first | omega | (dsimp only; omega)) (by first | omega | (dsimp only; omega))
                        (by first | omega | (dsimp only; omega)) hbtl hbt26 hbl26 hB hTokp hT ht2 cirH_mlr IHmp)
                    obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
                    try dsimp only at cirH_f3 cirH_n3
                    subst he3
                    cir_hrun_c hs2
                    subst hs2
                    refine ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, ?_⟩⟩
                    rw [← hmod, mp_plus _ _ _ _ _ (by omega) (by rw [← hPp]; exact hq0) (by rw [← hPp1]; omega), ← hPp]
                    exact ⟨cirH_u3, rfl, cirH_rg3,
                      by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3],
                      fun b hb1 hb2 => by
                        simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3 b hb1 (by omega),
                          cirH_frame b (by omega) (by omega) hb1 (by omega)],
                      by dsimp only [Mem.endScope]; omega⟩

      · -- `p = 29`: `pattern[1]` and `&pattern[2]` are past the end of `re_compiled`
        have cirH_Pp0 : P.toList[p]? = some P[p]! := by
          rw [Array.getElem?_toList, getElem!_pos P p (by omega)]; exact getElem?_pos P p (by omega)
        have cirH_Pp1 : P.toList[p + 1]? = none := by
          rw [Array.getElem?_toList]; exact getElem?_neg P (p + 1) (by omega)
        cir_hrun_c hs2
        all_goals omega
    · -- `p = 30`: `pattern[0]` is past the end of `re_compiled`
      have cirH_Pp0 : P.toList[p]? = none := by
        rw [Array.getElem?_toList]; exact getElem?_neg P p (by omega)
      cir_hrun_c hs2
  case main =>
    obtain ⟨⟨st1, σ1⟩, ⟨hnx1, hpost⟩, hk1⟩ := hw
    subst hs0
    rcases hpost with ⟨v, hst1, hmp⟩ | ⟨hst1, cirH_env1, cirH_names1, hmodel, cirH_fr, mlc1, cirH_bl1⟩
    · -- returned from inside the loop
      dsimp only at hst1 hnx1
      subst hst1
      cir_hrun_c hk1
      subst hk1
      obtain ⟨hu, he, hrg, hbl', hfr, hnx⟩ := hmp
      dsimp only at hbl' hfr hnx
      exact ⟨hu, he, hrg, by simp (disch := omega) only [Mem.endScope, killRange_of_lt, hbl'],
        fun b hb1 hb2 => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, hfr b hb1 hb2],
        by dsimp only [Mem.endScope]; omega⟩
    · -- the loop ended: `*matchlength = pre; return 0;`
      dsimp only at hst1 cirH_env1 cirH_names1 cirH_fr hnx1 cirH_bl1
      subst hst1
      have cirH_rv : σ1.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
        rw [cirH_fr m.next (by omega) (by omega) (by omega) (by omega)]
        simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      have cirH_mls : σ1.mem.blocks (m.next + 3) = some ⟨.stack, true, (Ty.int true 32).ptr, .ptr (.loc bl [])⟩ := by
        rw [cirH_fr (m.next + 3) (by omega) (by omega) (by omega) (by omega)]
        simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      have cirH_pre : σ1.mem.blocks (m.next + 4) = some ⟨.stack, true, .int true 32, .int ml⟩ := by
        rw [cirH_fr (m.next + 4) (by omega) (by omega) (by omega) (by omega)]
        simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      cir_hrun_c hk1
      subst hk1
      rw [hmodel]
      exact ⟨rfl, rfl, hml,
        by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same],
        fun b hb1 hb2 => by
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne,
            cirH_fr b (by omega) (by omega) hb1 (by omega)],
        by dsimp only [Mem.endScope]; omega⟩

/-- `matchpattern(&re_compiled[pi], text, matchlength)` for every pattern index up to 30, by
induction on `30 - pi`. -/
theorem matchpattern_pspec (P : Array Tok) (B : Array Nat) (hPs : P.size = 30)
    (hB : ∀ x ∈ B.toList, x < 256) (hP : ∀ (i : Nat) (hi : i < P.size), TokOK B P[i]) (pi : Nat)
    (hpi : pi ≤ 30) : MPC P B pi := by
  have key : ∀ n pi, 30 - pi ≤ n → pi ≤ 30 → MPC P B pi := by
    intro n
    induction n with
    | zero => exact fun pi h1 h2 => matchpattern_step P B pi hPs hB hP h2 (fun p' h3 h4 => absurd h4 (by omega))
    | succ n ih => exact fun pi h1 h2 => matchpattern_step P B pi hPs hB hP h2 (fun p' h3 h4 => ih p' (by omega) h4)
  exact key (30 - pi) pi (Nat.le_refl _) hpi

end EquivLean.Demo.XLang.TinyRegex.C
