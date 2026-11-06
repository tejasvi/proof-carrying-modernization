import EquivLean.Demo.XLang.TinyRegex.CPartial
import EquivLean.Demo.XLang.TinyRegex.CText
import EquivLean.Demo.XLang.TinyRegex.COneP
import EquivLean.Demo.Gen.Cir.TinyRegex

/-!
# tiny-regex-c → model, C side: `matchquestion` (partial correctness)

The matcher functions are specified by partial correctness (`pholds`): if the C returns, it
returns the model's result (`MPost`: no UB in the model, the result as 0/1, `*matchlength`).
The C runs in a hypothesis (`cir_hrun_c`); the calls of `matchpattern` use its contract as an
induction hypothesis, the calls of `matchone` its contract `matchone_pspec`.
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- The outcome of a match function as the model's `r`: no UB, `r.ok` returned as 1/0,
`*matchlength` (block `bl`) = `r.ml`, the caller's other blocks unchanged. -/
def MPost (r : EquivLean.Demo.XLang.TinyRegex.Res) (m : Mem) (bl : Nat) (kl : BlockKind) :
    Exit × Mem → Prop
  | (e, m') => r.ub = 0 ∧ e = .ret (some (.int (if r.ok then 1 else 0))) ∧
      (-2147483648 ≤ r.ml ∧ r.ml ≤ 2147483647) ∧ m'.blocks bl = some ⟨kl, true, .int true 32, .int r.ml⟩ ∧
      (∀ b, b ≠ bl → b < m.next → m'.blocks b = m.blocks b) ∧ m.next ≤ m'.next

/-! ### The model's `matchquestion`, by path -/

section
open EquivLean.Demo.XLang.TinyRegex (Ctx mpLoop matchquestion matchone rd chk UNUSED)
variable (C : Ctx) (tok : Tok) (pi ti : Nat) (ml : Int)

theorem mq_unused (h : tok.type = 0) (ub : Nat) : matchquestion C tok pi ti ml ub = ⟨true, ml, ub⟩ := by
  rw [matchquestion]; simp [UNUSED, h]

theorem mq_first (h0 : tok.type ≠ 0) (h1 : (mpLoop C ml pi ti ml 0).ok = true) :
    matchquestion C tok pi ti ml 0 = mpLoop C ml pi ti ml 0 := by
  rw [matchquestion]; simp [UNUSED, h0, h1]

theorem mq_end (h0 : tok.type ≠ 0) (h1 : (mpLoop C ml pi ti ml 0).ok = false) (hti : C.T.size ≤ ti)
    (hle : ti ≤ C.T.size) :
    matchquestion C tok pi ti ml 0 = ⟨false, (mpLoop C ml pi ti ml 0).ml, (mpLoop C ml pi ti ml 0).ub⟩ := by
  rw [matchquestion]
  have hr : rd C.T ti = (0, 0) := by
    unfold rd; rw [dite_eq_right (by omega), ite_eq_left (by omega)]
  simp [UNUSED, h0, h1, hr]

theorem mq_char (h0 : tok.type ≠ 0) (h1 : (mpLoop C ml pi ti ml 0).ok = false) (hti : ti < C.T.size)
    (hu1 : (mpLoop C ml pi ti ml 0).ub = 0) (hm2 : (matchone C tok C.T[ti]).2 = 0) (hc : C.T[ti] ≠ 0) :
    matchquestion C tok pi ti ml 0 =
      if (matchone C tok C.T[ti]).1 then
        (let r2 := mpLoop C (mpLoop C ml pi ti ml 0).ml pi (ti + 1) (mpLoop C ml pi ti ml 0).ml 0
         if r2.ok then ⟨true, r2.ml + 1, r2.ub ||| chk (r2.ml + 1)⟩ else ⟨false, r2.ml, r2.ub⟩)
      else ⟨false, (mpLoop C ml pi ti ml 0).ml, 0⟩ := by
  rw [matchquestion]
  have hr : rd C.T ti = (C.T[ti], 0) := by simp [rd, hti]
  simp only [UNUSED, beq_iff_eq, h0, ite_false, h1, Bool.false_eq_true, hr, hu1, Nat.zero_or, bne_iff_ne,
    ne_eq, hc, not_false_eq_true, ite_true, hm2]

end

theorem matchquestion_pspec (P : Array Tok) (B : Array Nat) (T : List Nat) (tok : Tok)
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
    pholds (evalCall ctx "matchquestion" [tokV 24 tok, .ptr (.loc 25 [.idx pi]),
      .ptr (.loc bt [.idx ti]), .ptr (.loc bl [])] m)
      (MPost (EquivLean.Demo.XLang.TinyRegex.matchquestion ⟨P, B, T.toArray⟩ tok pi ti ml 0) m bl kl) := by
  obtain ⟨es, tlen, cirH_tyt⟩ := htyt
  intro r hr
  have hs : (evalCall ctx "matchquestion" [tokV 24 tok, .ptr (.loc 25 [.idx pi]),
      .ptr (.loc bt [.idx ti]), .ptr (.loc bl [])] m).holds (· = r) := by rw [hr]; rfl
  have cirH_tv0 : (tokV 24 tok).get? [.idx 0] = some (.int tok.type) := by unfold tokV; split <;> rfl
  have cirH_ty : (tok.type : Int) ≤ 255 := by have := hTok.1; omega
  have cirH_t0 : ∀ n : Nat, ((n : Int) + 0).toNat = n := fun n => by omega
  have cirH_t1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  have cirH_tg : ∀ (i : Nat) (h : i < (patL T).length), (patL T)[i] = (patL T).getD i 0 :=
    fun i h => getElem_eq_getD h
  have cirH_len : (patL T).length = T.length + 1 := patL_length T
  have cirH_ne : bt ≠ bl := hbtl
  have cirH_c0 := (patL_char hT ti).1
  have cirH_z0 := (patL_char hT ti).2
  have cirH_c1 := (patL_char hT (ti + 1)).1
  have cirH_z1 := (patL_char hT (ti + 1)).2
  cir_hstep hs
  cir_hrun_c hs
  · -- `matchpattern(pattern, text, matchlength)`
    obtain ⟨⟨e1, m6⟩, -, hp1, hs⟩ := holds_pspec_elim hs (IHmp ti ml _ hti hml
      (by simp (disch := omega) only [upd_apply_ne, hl]) (by simp (disch := omega) only [upd_apply_ne])
      (by simp (disch := omega) only [upd_apply_ne]) (by simp (disch := omega) only [upd_apply_ne])
      (by simp))
    obtain ⟨cirH_u1, he1, cirH_rg1, cirH_m1, cirH_f1, cirH_n1⟩ := hp1
    dsimp only at cirH_f1 cirH_n1
    subst he1
    have h0 : tok.type ≠ 0 := by omega
    cir_hrun_c hs
    · -- the text is at its end: return 0
      subst hs
      have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ok = false := by
        simp_all
      have hend : T.length ≤ ti := by simp only [bne_iff_ne, ne_eq] at *; omega
      rw [mq_end _ _ _ _ _ h0 hok (by simpa using hend) (by simpa using hti)]
      refine ⟨cirH_u1, rfl, cirH_rg1, ?_, ?_, ?_⟩
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m1]
      · intro b hb1 hb2
        simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1]
      · simp only [Mem.endScope]; omega
    · -- `matchone(p, *text++)`
      have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ok = false := by
        simp_all
      have hlt : ti < T.length := by simp only [bne_iff_ne, ne_eq] at *; omega
      have hbyte : (patL T).getD ti 0 = sc T.toArray[ti] := by
        rw [patL_getD_lt hlt]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      have hb256 : T.toArray[ti] < 256 := (hT _ (by simp)).2
      have hb0 : T.toArray[ti] ≠ 0 := by have := (hT _ (by simp : T.toArray[ti] ∈ T)).1; omega
      obtain ⟨⟨e2, m7⟩, -, ⟨hmu, w2, cirH_v2, cirH_r2a, cirH_r2b, cirH_r2c, cirH_fr2b, cirH_fr2a⟩, hs⟩ :=
        holds_pspec_elim hs (matchone_pspec ⟨P, B, T.toArray⟩ tok T.toArray[ti] _ kC _
          (by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1, hC])
          (by dsimp only; omega) hB hTok (by omega) hb256 hbyte)
      dsimp only at cirH_v2 cirH_fr2a cirH_fr2b
      subst cirH_v2
      have hmodel := mq_char ⟨P, B, T.toArray⟩ tok pi ti ml h0 hok (by simpa using hlt) cirH_u1 hmu hb0
      cir_hrun_c hs
      · -- `matchone` failed: return 0
        subst hs
        have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[ti]).1 = false := by
          cases hh : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[ti]).1
          · rfl
          · exfalso; simp only [bne_iff_ne, ne_eq] at *; exact absurd (cirH_r2c.2 hh) (by omega)
        rw [hmodel, hm]
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨rfl, rfl, cirH_rg1, ?_, ?_, ?_⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_m1]
        · intro b hb1 hb2
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_f1]
        · simp only [Mem.endScope]; omega
      · -- `matchpattern(pattern, text, matchlength)` after the character
        have hm : (EquivLean.Demo.XLang.TinyRegex.matchone ⟨P, B, T.toArray⟩ tok T.toArray[ti]).1 = true := by
          apply cirH_r2c.1; simp only [bne_iff_ne, ne_eq] at *; omega
        obtain ⟨⟨e3, m9⟩, -, hp3, hs⟩ := holds_pspec_elim hs (IHmp (ti + 1) _ _ (by omega) cirH_rg1
          (by simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_m1])
          (by simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_f1])
          (by simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_f1])
          (by simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr2b, cirH_f1])
          (by simp only []; omega))
        obtain ⟨cirH_u3, he3, cirH_rg3, cirH_m3, cirH_f3, cirH_n3⟩ := hp3
        dsimp only at cirH_f3 cirH_n3
        subst he3
        rw [hm] at hmodel
        cir_hrun_c hs
        · -- the rest did not match: return 0
          subst hs
          have hok2 : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩
              (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ml pi (ti + 1)
              (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ml 0).ok = false := by
            simp_all
          rw [hmodel]
          simp only [ite_true, hok2, Bool.false_eq_true, ite_false]
          refine ⟨cirH_u3, rfl, cirH_rg3, ?_, ?_, ?_⟩
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m3]
          · intro b hb1 hb2
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3, cirH_fr2b,
              cirH_f1]
          · simp only [Mem.endScope]; omega
        · -- the rest matched: `(*matchlength)++`, return 1
          subst hs
          have hok2 : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩
              (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ml pi (ti + 1)
              (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ml 0).ok = true := by
            simp_all
          rw [hmodel]
          simp only [ite_true, hok2]
          refine ⟨?_, rfl, cirA_br6, ?_, ?_, ?_⟩
          · simp only [cirH_u3, EquivLean.Demo.XLang.TinyRegex.chk, EquivLean.Demo.XLang.TinyRegex.INT_MIN,
              EquivLean.Demo.XLang.TinyRegex.INT_MAX, cirA_br6, and_self, ite_true, Nat.zero_or]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
          · intro b hb1 hb2
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3, cirH_fr2b,
              cirH_f1]
          · simp only [Mem.endScope]; omega
    · -- `matchpattern` matched: return 1
      subst hs
      have hok : (EquivLean.Demo.XLang.TinyRegex.mpLoop ⟨P, B, T.toArray⟩ ml pi ti ml 0).ok = true := by
        simp_all
      rw [mq_first _ _ _ _ _ h0 hok]
      refine ⟨cirH_u1, by simp [hok], cirH_rg1, ?_, ?_, ?_⟩
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_m1]
      · intro b hb1 hb2
        simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1]
      · simp only [Mem.endScope]; omega
  · -- `p.type == UNUSED`: return 1
    subst hs
    have e0 : tok.type = 0 := by omega
    rw [mq_unused _ _ _ _ _ e0]
    refine ⟨rfl, rfl, hml, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, hl]
    · intro b hb1 hb2
      simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]
    · simp only [Mem.endScope]; omega

end EquivLean.Demo.XLang.TinyRegex.C
