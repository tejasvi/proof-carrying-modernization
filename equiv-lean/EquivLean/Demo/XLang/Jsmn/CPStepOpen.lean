import EquivLean.Demo.XLang.Jsmn.CPLemmas

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on `{` and `[`

`step_open`: `count++`, a new token (`jsmn_alloc_token`, inlined; `JSMN_ERROR_NOMEM` without one), the parent's
`size++` when `toksuper != -1`, the type and start of the new token, `toksuper = toknext - 1`, per the model's `step`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop incSize bumpSup dflt OBJECT ARRAY ERROR_NOMEM)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

theorem step_open (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 123 ∨ byteAt js st.pos = 91) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hL := hwf.len_n
  have hpos := hwf.pos_le
  have htp := hwf.len_pos
  have hsup := hwf.sup
  have cirH_tv : ∀ t : Tok, tokV t = .agg [.int t.type, .int t.start, .int t.stop, .int t.size] := fun t => rfl
  have cirH_tg : ∀ i, i < st.toks.length → (tokArr st.toks n)[i]? = some (tokV (st.toks.getD i dflt)) :=
    fun i h => tokArr_get_lt _ _ _ h
  have cirH_t0 : tok0 = .agg [.undef, .undef, .undef, .undef] := rfl
  have cirH_tl : (tokArr st.toks n).length = n := tokArr_length _ _ hL
  have hlpos := hl.1
  rcases hc with hc | hc
  all_goals (
    have cirH_c := hc
    by_cases hfull : n ≤ st.toks.length
    · -- no token left: `JSMN_ERROR_NOMEM`
      have cirH_full : (n : Int) ≤ (st.toks.length : Int) := by omega
      have hstep : step js n st = .error ERROR_NOMEM := by unfold step; simp [hc, hfull]
      cir_hrun_c hs
      try (simp only [evalOp] at hs; cir_hrun_c hs)
      cir_hstep hs
      cir_hrun_c hs
      all_goals (
        subst hs
        refine ⟨⟨ERROR_NOMEM, hstep, rfl⟩, ⟨st.toks, hL, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
        ps_close)
    · have cirH_full : ¬ ((n : Int) ≤ (st.toks.length : Int)) := by omega
      have cirH_tn : (tokArr st.toks n)[st.toks.length]? = some tok0 := tokArr_get_next _ _ (by omega)
      have cirH_tb0 : (0 : Int) ≤ (st.toks.length : Int) := by omega
      have cirH_tb1 : (st.toks.length : Int) ≤ (n : Int) := by omega
      have hstep : step js n st = .ok ⟨st.pos + 1, bumpSup st.toks st.sup ++
          [⟨if byteAt js st.pos = 123 then OBJECT else ARRAY, st.pos, -1, 0⟩], st.toks.length⟩ := by
        unfold step; simp [hc, hfull]
      rcases hsup with hs1 | ⟨hs1, hs2⟩
      · -- no parent
        have cirH_sup : st.sup = -1 := hs1
        cir_hrun_c hs
        simp only [evalOp] at hs
        cir_hrun_c hs
        cir_hstep hs
        cir_hrun_c hs
        all_goals (
          subst hs
          refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_, fun b hb h1 h2 => ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨.ptr (.loc bt [.idx st.toks.length]), ?_⟩, ?_, ?_, ?_⟩⟩
          ps_close
          all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
            upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
            List.length_append, List.length_cons, List.length_nil, bumpSup_length, and_true, true_and]; omega))
          all_goals (simp (config := { decide := true }) (disch := omega) only [Mem.endScope, killRange_self,
            killRange_of_lt, upd_apply_ne, upd_apply_same, tokArr_push1, tokArr_open0', cirH_sup, bumpSup_neg, hc,
            OBJECT, ARRAY, ite_true, ite_false, eq_self_iff_true]))
      · -- the parent `toksuper`: its size grows
        have cirH_sup : ¬ (st.sup = -1) := by omega
        have cirH_si : st.sup.toNat < st.toks.length := by omega
        have hr := tok_ranges hwf cirH_si
        cir_hrun_c hs
        simp only [evalOp] at hs
        cir_hrun_c hs
        cir_hstep hs
        cir_hrun_c hs
        all_goals (
          subst hs
          refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_, fun b hb h1 h2 => ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨.ptr (.loc bt [.idx st.toks.length]), ?_⟩, ?_, ?_, ?_⟩⟩
          ps_close
          all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
            upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
            List.length_append, List.length_cons, List.length_nil, bumpSup_length, and_true, true_and]; omega))
          all_goals (simp (config := { decide := true }) (disch := omega) only [Mem.endScope, killRange_self,
            killRange_of_lt, upd_apply_ne, upd_apply_same, tokArr_open', bumpSup_eq _ _ cirH_sup, hc, OBJECT, ARRAY,
            ite_true, ite_false, eq_self_iff_true])))

end EquivLean.Demo.XLang.Jsmn.C
