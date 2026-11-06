import EquivLean.Demo.XLang.Jsmn.CPLemmas
import EquivLean.Demo.XLang.Jsmn.CSearch

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on `,`

`step_comma`: one turn of the main loop on `,`: when `toksuper` is a token other than an object or an array, the
backward search for the last open object or array (`comma_search_elim`) gives the new `toksuper`; `pos++`, per the
model's `step`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop dflt lastOpenCont ARRAY OBJECT)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

set_option hygiene false in
/-- Closes the goals of `step_comma` after the search: the loop head's facts, through the search's frame
`cirH_fr3` and its `i` slot `cirH_I2`. -/
macro "cm_close" : tactic => `(tactic| (
  all_goals (try (dsimp only [Mem.endScope]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, cirH_fr3, cirH_I2, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, htb, hfr]; done))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
    List.length_append, List.length_cons, List.length_nil, and_true, true_and]; omega))))

set_option maxHeartbeats 2000000000 in
theorem step_comma (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 44) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hL := hwf.len_n
  have hpos := hwf.pos_le
  have hLp := hwf.len_pos
  have hsup := hwf.sup
  have cirH_c := hc
  have cirH_tv : ∀ t : Tok, tokV t = .agg [.int t.type, .int t.start, .int t.stop, .int t.size] := fun t => rfl
  have cirH_tg : ∀ i, i < st.toks.length → (tokArr st.toks n)[i]? = some (tokV (st.toks.getD i dflt)) :=
    fun i h => tokArr_get_lt _ _ _ h
  have cirH_tl : (tokArr st.toks n).length = n := tokArr_length _ _ hL
  rcases hsup with hs1 | ⟨hs1, hs2⟩
  · -- no `toksuper`: nothing but `pos++`
    have cirH_sup : st.sup = -1 := hs1
    have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
      rw [EquivLean.Demo.XLang.Jsmn.step_comma hc, if_neg (fun h => h.1 hs1)]
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    all_goals (
      subst hs
      refine ⟨⟨st.pos + 1, st.toks, st.sup⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
        fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
      ps_close)
  · have cirH_sup : ¬ (st.sup = -1) := by omega
    have cirH_si : st.sup.toNat < st.toks.length := by omega
    have hr := tok_ranges hwf cirH_si
    by_cases hA : (st.toks.getD st.sup.toNat dflt).type = 2
    · -- `toksuper` is an array: nothing but `pos++`
      have cirH_A := hA
      have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_comma hc, if_neg (fun h => h.2.1 (by simp only [hA, ARRAY]))]
      cir_hrun_c hs
      try (simp only [evalOp] at hs; cir_hrun_c hs)
      all_goals (
        subst hs
        refine ⟨⟨st.pos + 1, st.toks, st.sup⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        ps_close)
    by_cases hO : (st.toks.getD st.sup.toNat dflt).type = 1
    · -- `toksuper` is an object: nothing but `pos++`
      have cirH_O := hO
      have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_comma hc, if_neg (fun h => h.2.2 (by simp only [hO, OBJECT]))]
      cir_hrun_c hs
      try (simp only [evalOp] at hs; cir_hrun_c hs)
      all_goals (
        subst hs
        refine ⟨⟨st.pos + 1, st.toks, st.sup⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        ps_close)
    -- a key or a value under `toksuper`: the backward search for the last open object or array
    have cirH_nA : ¬ ((st.toks.getD st.sup.toNat dflt).type = 2) := hA
    have cirH_nO : ¬ ((st.toks.getD st.sup.toNat dflt).type = 1) := hO
    have cirH_ssw := scan_start_wrap st.toks.length (by omega)
    have hcond : st.sup ≠ -1 ∧ (st.toks.getD st.sup.toNat dflt).type ≠ ARRAY ∧
        (st.toks.getD st.sup.toNat dflt).type ≠ OBJECT :=
      ⟨cirH_sup, fun h => hA (by simpa only [ARRAY] using h), fun h => hO (by simpa only [OBJECT] using h)⟩
    have hrng : TokRange st.toks := by
      intro t ht
      obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hwf.tok t ht
      simp only [OBJECT, ARRAY, Jsmn.STRING, Jsmn.PRIMITIVE] at h1
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    all_goals (
      obtain ⟨⟨a1, mem2, env2, names2⟩, hK, ha1, henv, hnm2, hnx2, hfr2, ⟨vI, hI2⟩, hpb2⟩ :=
        comma_search_elim st.toks n st.pos st.sup bp bt (m.next + 1) (m.next + 4) (m.next + 7) kp kt
          hs
          (by simp only [upd]; exact e6) (by simp only [upd]; exact e9) (by simp only [upd]; exact e12)
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, l1])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, l4])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, hpb, parserV])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, htb])
          hkp (by omega) hrng (by omega) (by omega) (by omega) (by omega)
          (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
          (by dsimp only; omega)
      dsimp only at ha1 henv hnm2 hnx2 hfr2 hI2 hpb2 hK
      subst ha1 henv hnm2
      have cirH_fr3 : ∀ b, b ≠ m.next + 7 → b ≠ bp → b < σ.mem.next → mem2.blocks b = σ.mem.blocks b :=
        fun b h1 h2 h3 => by
          rw [hfr2 b h1 h2 (by omega)]
          simp (disch := omega) only [upd_apply_ne]
      have cirH_I2 := hI2
      rcases hlo : lastOpenCont st.toks st.toks.length with _ | i
      · -- no open object or array: `toksuper` stays
        simp only [hlo, parserV] at hpb2
        have cirH_pb3 := hpb2
        have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
          rw [EquivLean.Demo.XLang.Jsmn.step_comma hc, if_pos hcond]
          simp only [hlo]
        cir_hrun_c hK
        all_goals (
          subst hK
          refine ⟨⟨st.pos + 1, st.toks, st.sup⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
            fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨vI, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
          cm_close)
      · -- `toksuper` becomes the last open object or array `i`
        simp only [hlo, parserV] at hpb2
        have cirH_pb3 := hpb2
        have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, (i : Int)⟩ := by
          rw [EquivLean.Demo.XLang.Jsmn.step_comma hc, if_pos hcond]
          simp only [hlo]
        cir_hrun_c hK
        all_goals (
          subst hK
          refine ⟨⟨st.pos + 1, st.toks, (i : Int)⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
            fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨vI, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
          cm_close))

end EquivLean.Demo.XLang.Jsmn.C
