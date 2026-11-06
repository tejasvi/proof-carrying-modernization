import EquivLean.Demo.XLang.TinyRegex.CMatchS

/-!
# tiny-regex-c → model, C side: `matchplus` (partial correctness)

As `matchstar` (`CMatchS.lean`), with the second loop down to one character after `prepoint`
(`text > prepoint`, the model's `plusBack`) and no restore of `*matchlength`.
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

section
open EquivLean.Demo.XLang.TinyRegex (Ctx advance plusBack matchplus mpLoop matchone chk)
variable (C : Ctx) (p : Tok) (pi pre : Nat)

theorem pb_ok (t : Nat) (mlc : Int) (h : pre < t) (hr : (mpLoop C mlc pi t mlc 0).ok = true) :
    plusBack C pi pre t mlc 0 = mpLoop C mlc pi t mlc 0 := by
  rw [plusBack]; simp [h, hr]

theorem pb_next (t : Nat) (mlc : Int) (h : pre < t) (hr : (mpLoop C mlc pi t mlc 0).ok = false)
    (hu : (mpLoop C mlc pi t mlc 0).ub = 0) (hov : chk ((mpLoop C mlc pi t mlc 0).ml - 1) = 0) :
    plusBack C pi pre t mlc 0 = plusBack C pi pre (t - 1) ((mpLoop C mlc pi t mlc 0).ml - 1) 0 := by
  rw [plusBack]; simp [h, hr, hu, hov]

theorem pb_exit (t : Nat) (mlc : Int) (h : t ≤ pre) : plusBack C pi pre t mlc 0 = ⟨false, mlc, 0⟩ := by
  rw [plusBack]; simp [show ¬ pre < t by omega]

theorem mpl_unfold (ti : Nat) (ml : Int) :
    matchplus C p pi ti ml 0 = plusBack C pi ti (advance C p ti ml 0).1 (advance C p ti ml 0).2.1
      (advance C p ti ml 0).2.2 := by
  rw [matchplus]

end

theorem matchplus_pspec (P : Array Tok) (B : Array Nat) (T : List Nat) (tok : Tok)
    (pi ti bt bl : Nat) (ml : Int) (m : Mem) (kt kl kR kC : BlockKind) (tyt : Ty)
    (hR : m.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩)
    (hC : m.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
      .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩)
    (ht : m.blocks bt = some ⟨kt, true, tyt, .arr ((patL T).map .int)⟩)
    (htyt : ∃ es tlen, tyt = .array (.int es 8) tlen)
    (hl : m.blocks bl = some ⟨kl, true, .int true 32, .int ml⟩) (hkl : kl ≠ .readonly)
    (hn : 26 ≤ m.next) (hbt : bt < m.next) (hbl : bl < m.next) (hbtl : bt ≠ bl) (hbt26 : 26 ≤ bt)
    (hbl26 : 26 ≤ bl) (hB : ∀ x ∈ B.toList, x < 256) (hTok : TokOK B tok)
    (hT : ∀ b ∈ T, 0 < b ∧ b < 256) (hti : ti ≤ T.length)
    (hml : -2147483648 ≤ ml ∧ ml ≤ 2147483647)
    (IHmp : ∀ (t' : Nat) (ml' : Int) (m' : Mem), t' ≤ T.length → -2147483648 ≤ ml' ∧ ml' ≤ 2147483647 →
      m'.blocks bl = some ⟨kl, true, .int true 32, .int ml'⟩ → m'.blocks 25 = m.blocks 25 →
      m'.blocks 24 = m.blocks 24 → m'.blocks bt = m.blocks bt → m.next ≤ m'.next →
      pholds (evalCall ctx "matchpattern" [.ptr (.loc 25 [.idx pi]), .ptr (.loc bt [.idx t']),
        .ptr (.loc bl [])] m')
        (MPost (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml' pi t' ml' 0) m' bl kl)) :
    pholds (evalCall ctx "matchplus" [tokV 24 tok, .ptr (.loc 25 [.idx pi]),
      .ptr (.loc bt [.idx ti]), .ptr (.loc bl [])] m)
      (MPost (EquivLean.Demo.XLang.TinyRegex.matchplus ⟨P, B, T.toArray⟩ tok pi ti ml 0) m bl kl) := by
  obtain ⟨es, tlen, cirH_tyt⟩ := htyt
  intro r hr
  have hs : (evalCall ctx "matchplus" [tokV 24 tok, .ptr (.loc 25 [.idx pi]),
      .ptr (.loc bt [.idx ti]), .ptr (.loc bl [])] m).holds (· = r) := by rw [hr]; rfl
  have cirH_ne : bt ≠ bl := hbtl
  have cirH_t0 : ∀ n : Nat, ((n : Int) + 0).toNat = n := fun n => by omega
  have cirH_t1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  have cirH_tg : ∀ (i : Nat) (h : i < (patL T).length), (patL T)[i] = (patL T).getD i 0 :=
    fun i h => getElem_eq_getD h
  have cirH_len : (patL T).length = T.length + 1 := patL_length T
  cir_hstep hs
  cir_hrun_c hs
  -- the first loop
  all_goals (try (obtain ⟨s0, hs0, hs⟩ := holds_while_name hs))
  · refine (fun hw => ?main) (holds_while_inv hs
      (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ s0.mem.next ≤ σ.mem.next ∧
        (∀ b, b ≠ m.next + 3 → b ≠ bl → b < s0.mem.next → σ.mem.blocks b = s0.mem.blocks b) ∧
        ∃ (t : Nat) (mlc : Int), σ.mem.blocks (m.next + 3) =
            some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bt [.idx t])⟩ ∧
          σ.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧ ti ≤ t ∧ t ≤ T.length ∧
          (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
          EquivLean.Demo.XLang.TinyRegex.advance ⟨P, B, T.toArray⟩ tok t mlc 0 =
            EquivLean.Demo.XLang.TinyRegex.advance ⟨P, B, T.toArray⟩ tok ti ml 0)
      (fun a => a.1 = .next ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧ s0.mem.next ≤ a.2.mem.next ∧
        (∀ b, b ≠ m.next + 3 → b ≠ bl → b < s0.mem.next → a.2.mem.blocks b = s0.mem.blocks b) ∧
        ∃ (t : Nat) (mlc : Int), a.2.mem.blocks (m.next + 3) =
            some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bt [.idx t])⟩ ∧
          a.2.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧ ti ≤ t ∧ t ≤ T.length ∧
          (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
          EquivLean.Demo.XLang.TinyRegex.advance ⟨P, B, T.toArray⟩ tok ti ml 0 = (t, mlc, 0))
      ?init ?step)
    case init =>
      subst hs0
      refine ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ => rfl, ti, ml, ?_, ?_, Nat.le_refl _, hti, hml, rfl⟩
      · simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      · simp (disch := omega) only [upd_apply_ne, hl]
    case step =>
      intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, t, mlc, cirH_slot, cirH_bl, ht1, ht2, cirH_mlr, hadv⟩ r2 hr2
      have hs2 := holds_of_eq_ok hr2
      have cirH_ct := (patL_char hT t).1
      have cirH_zt := (patL_char hT t).2
      subst hs0
      unfold whileIter at hs2
      cir_hrun_c hs2
      · -- the text is at its end: the loop exits
        subst hs2
        have hte : t = T.length := by have := cirH_zt; simp only [bne_iff_ne, ne_eq] at *; omega
        refine ⟨rfl, rfl, rfl, cirH_nx, cirH_frame, t, mlc, cirH_slot, cirH_bl, ht1, ht2, cirH_mlr, ?_⟩
        rw [← hadv]; exact adv_end _ _ _ _ (by simpa using hte)
      · -- `matchone(p, *text)`
        have hlt : t < T.length := by have := cirH_zt; simp only [bne_iff_ne, ne_eq] at *; omega
        have hbyte : (patL T).getD t 0 = sc T.toArray[t] := by
          rw [patL_getD_lt hlt]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        have hb256 : T.toArray[t] < 256 := (hT _ (by simp)).2
        have hb0 : T.toArray[t] ≠ 0 := by have := (hT _ (by simp : T.toArray[t] ∈ T)).1; omega
        have cirH_c24 : σ.mem.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
            .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩ := by
          rw [cirH_frame 24 (by omega) (by omega) (by first | omega | (dsimp only; omega))]
          simp (disch := omega) only [upd_apply_ne, hC]
        obtain ⟨⟨e2, m7⟩, -, ⟨hmu, w2, cirH_v2, cirH_r2a, cirH_r2b, cirH_r2c, cirH_fr2b, cirH_fr2a⟩, hs2⟩ :=
          holds_pspec_elim hs2 (matchone_pspec ⟨P, B, T.toArray⟩ tok T.toArray[t] _ kC _
            (by first | exact cirH_c24 | simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_c24])
            (by first | omega | (dsimp only at cirH_nx ⊢; omega)) hB hTok (by omega) hb256 hbyte)
        dsimp only at cirH_v2 cirH_fr2a cirH_fr2b
        subst cirH_v2
        cir_hrun_c hs2
        all_goals (subst hs2; by_cases hw : w2 = 0)
        all_goals (try (exfalso; simp only [Exit.cond.injEq, bne_iff_ne, bne_eq_false_iff_eq, ne_eq] at *; omega))
        · -- `matchone` failed: the loop exits
          have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[t]).1 = false := by
            cases hh : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[t]).1
            · rfl
            · exact absurd (cirH_r2c.2 hh) (by omega)
          refine ⟨rfl, rfl, rfl, by dsimp only at cirH_nx ⊢; omega, ?_, t, mlc, ?_, ?_, ht1, ht2, cirH_mlr, ?_⟩
          · intro b hb1 hb2 hb3
            have hb4 := cirH_frame b hb1 hb2 hb3
            simp (disch := omega) only [killRange_of_lt, cirH_fr2b, hb4]
          · simp (disch := omega) only [killRange_of_lt, cirH_fr2b, cirH_slot]
          · simp (disch := omega) only [killRange_of_lt, cirH_fr2b, cirH_bl]
          · rw [← hadv]; exact adv_nomatch _ _ _ _ (by simpa using hlt) hb0 hm hmu
        · -- `matchone` matched: `text++; (*matchlength)++;`, the loop continues
          have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[t]).1 = true :=
            cirH_r2c.1 hw
          have hov : -2147483648 ≤ mlc + 1 ∧ mlc + 1 ≤ 2147483647 := ‹_›
          refine ⟨rfl, rfl, by dsimp only [Mem.endScope] at cirH_nx ⊢; omega, ?_, t + 1, mlc + 1, ?_, ?_, by omega, by omega, hov, ?_⟩
          · intro b hb1 hb2 hb3
            have hb4 := cirH_frame b hb1 hb2 hb3
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, hb4]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same]
          · rw [← hadv]
            exact (adv_step _ _ _ _ (by simpa using hlt) hb0 hm hmu (by
              simp only [EquivLean.Demo.XLang.TinyRegex.chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN,
                EquivLean.Demo.XLang.TinyRegex.INT_MAX, hov, and_self, ite_true])).symm
    case main =>
      obtain ⟨⟨st1, σ1⟩, ⟨hst1, cirH_env1, cirH_names1, cirH_nx1, cirH_frame1, t1, mlc1, cirH_slot1, cirH_bl1,
        ht11, ht12, cirH_mlr1, hadv1⟩, hk1⟩ := hw
      dsimp only at hst1
      subst hst1
      clear hs
      subst hs0
      dsimp only at cirH_env1 cirH_names1 cirH_nx1 cirH_frame1 cirH_slot1 cirH_bl1
      cir_hrun_c hk1
      -- the second loop: back off down to `prepoint`
      obtain ⟨s1, hs1, hk1⟩ := holds_while_name hk1
      refine (fun hw2 => ?main2) (holds_while_inv hk1
        (fun σ => σ.env = s1.env ∧ σ.names = s1.names ∧ s1.mem.next ≤ σ.mem.next ∧
          (∀ b, b ≠ m.next + 3 → b ≠ bl → b < s1.mem.next → σ.mem.blocks b = s1.mem.blocks b) ∧
          ∃ (t : Nat) (mlc : Int), σ.mem.blocks (m.next + 3) =
              some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bt [.idx t])⟩ ∧
            σ.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧ t ≤ t1 ∧ ti ≤ t ∧
            (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
            EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t mlc 0 =
              EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0)
        (fun a =>
          (a.1 = .exit (.ret (some (.int 1))) ∧
            (EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0).ok = true ∧
            (EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0).ub = 0 ∧
            (-2147483648 ≤ (EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0).ml ∧
              (EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0).ml ≤ 2147483647) ∧
            a.2.mem.blocks bl = some ⟨kl, true, .int true 32,
              .int (EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0).ml⟩ ∧
            (∀ b, b ≠ bl → b < m.next → a.2.mem.blocks b = m.blocks b) ∧
            s1.mem.next ≤ a.2.mem.next) ∨
          (a.1 = .next ∧ a.2.env = s1.env ∧ a.2.names = s1.names ∧
            (∀ b, b ≠ m.next + 3 → b ≠ bl → b < s1.mem.next → a.2.mem.blocks b = s1.mem.blocks b) ∧
            s1.mem.next ≤ a.2.mem.next ∧ ∃ (mlc : Int), a.2.mem.blocks bl = some ⟨kl, true, .int true 32, .int mlc⟩ ∧
              (-2147483648 ≤ mlc ∧ mlc ≤ 2147483647) ∧
              EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0 = ⟨false, mlc, 0⟩))
        ?init2 ?step2)
      case init2 =>
        subst hs1
        refine ⟨rfl, rfl, Nat.le_refl _, fun b _ _ _ => rfl, t1, mlc1, ?_, ?_, Nat.le_refl _, ht11,
          cirH_mlr1, rfl⟩
        · simp (disch := omega) only [killRange_of_lt, cirH_slot1]
        · simp (disch := omega) only [killRange_of_lt, cirH_bl1]
      case step2 =>
        intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, t, mlc, cirH_slot, cirH_bl, ht1, ht2, cirH_mlr, hsb⟩ r2 hr2
        have hs2 := holds_of_eq_ok hr2
        have cirH_ct := (patL_char hT t).1
        have cirH_zt := (patL_char hT t).2
        subst hs1
        dsimp only at cirH_env cirH_names cirH_nx cirH_frame
        unfold whileIter at hs2
        cir_hrun_c hs2
        · -- `matchpattern(pattern, text--, matchlength)`
          obtain ⟨⟨e3, m9⟩, -, hp3, hs2⟩ := holds_pspec_elim hs2 (IHmp t mlc _ (by omega) cirH_mlr
            (by simp (disch := omega) only [upd_apply_ne, cirH_bl])
            (by simp (disch := omega) only [upd_apply_ne, cirH_frame, killRange_of_lt, cirH_frame1])
            (by simp (disch := omega) only [upd_apply_ne, cirH_frame, killRange_of_lt, cirH_frame1])
            (by simp (disch := omega) only [upd_apply_ne, cirH_frame, killRange_of_lt, cirH_frame1])
            (by dsimp only; omega))
          obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
          dsimp only at cirH_f3 cirH_n3
          subst he3
          have ht0 : 1 ≤ t := by omega
          have htt : ti < t := by omega
          have cirH_tm : ((t : Int) + -1).toNat = t - 1 := by omega
          cir_hrun_c hs2
          · -- no match at `t`: `(*matchlength)--`, the loop continues
            subst hs2
            have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0).ok = false := by
              simp_all
            have hov : -2147483648 ≤ (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0).ml - 1 ∧
                (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0).ml - 1 ≤ 2147483647 := ‹_›
            refine ⟨rfl, rfl, by dsimp only [Mem.endScope] at cirH_nx cirH_n3 ⊢; omega, ?_, t - 1,
              (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0).ml - 1, ?_, ?_,
              by omega, by omega, hov, ?_⟩
            · intro b hb1 hb2 hb3
              dsimp only at hb3
              simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne, cirH_f3, cirH_frame]
            · simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne, upd_apply_same, cirH_f3,
                cirH_tm]
            · simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_same]
            · rw [← hsb]
              exact (pb_next _ _ _ _ _ htt hok cirH_u3 (by
                simp only [EquivLean.Demo.XLang.TinyRegex.chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN,
                  EquivLean.Demo.XLang.TinyRegex.INT_MAX, hov, and_self, ite_true])).symm
          · -- a match at `t`: return 1
            subst hs2
            have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0).ok = true := by
              simp_all
            have hR : EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0 =
                EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ mlc pi t mlc 0 := by
              rw [← hsb]; exact pb_ok _ _ _ _ _ htt hok
            refine Or.inl ⟨rfl, by rw [hR]; exact hok, by rw [hR]; exact cirH_u3, by rw [hR]; exact cirH_rg3, ?_, ?_, ?_⟩
            · rw [hR]; simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne, cirH_m3]
            · intro b hb1 hb2
              simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne, cirH_f3,
                cirH_frame, cirH_frame1]
            · dsimp only [Mem.endScope] at cirH_nx cirH_n3 ⊢; omega
        · -- `text < prepoint`: the loop exits
          subst hs2
          refine Or.inr ⟨rfl, rfl, rfl, cirH_frame, cirH_nx, mlc, cirH_bl, cirH_mlr, ?_⟩
          rw [← hsb]; exact pb_exit _ _ _ _ _ (by omega)
      case main2 =>
        have hmodel : EquivLean.Demo.XLang.TinyRegex.matchplus ⟨P, B, T.toArray⟩ tok pi ti ml 0 =
            EquivLean.Demo.XLang.TinyRegex.plusBack ⟨P, B, T.toArray⟩ pi ti t1 mlc1 0 := by
          rw [mpl_unfold, hadv1]
        obtain ⟨⟨st2, σ2⟩, hpost2, hk2⟩ := hw2
        clear hk1
        subst hs1
        rcases hpost2 with ⟨hst2, hok2, hub2, hrg2, hbl2, hfr2, hnx2⟩ | ⟨hst2, henv2, hnames2, hfr2, hnx2, mlc2, hbl2, hrg2, hR2⟩
        · -- a match: return 1
          dsimp only at hst2 hbl2 hfr2 hnx2
          subst hst2
          cir_hrun_c hk2
          subst hk2
          rw [hmodel]
          refine ⟨hub2, by simp [hok2], hrg2, ?_, ?_, ?_⟩
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, hbl2]
          · intro b hb1 hb2
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, hfr2 b hb1 hb2]
          · simp only [Mem.endScope]; omega
        · -- no match down to `prepoint`: `return 0;`
          dsimp only at hst2 henv2 hnames2 hfr2 hnx2 hbl2
          subst hst2
          cir_hrun_c hk2
          subst hk2
          rw [hmodel, hR2]
          refine ⟨rfl, rfl, hrg2, ?_, ?_, ?_⟩
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same, hbl2]
          · intro b hb1 hb2
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, hfr2,
              cirH_frame1]
          · simp only [Mem.endScope]; omega

end EquivLean.Demo.XLang.TinyRegex.C
