import EquivLean.Demo.XLang.Jsmn.CPLemmas
import EquivLean.Demo.XLang.Jsmn.CSearch

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on `}` and `]`

`step_close`: one turn of the main loop on a closing bracket, per the model's `step`
(`ModelStep.step_close_none`, `step_close_some`): the first backward search for the last open token
(`close_first_elim`): none, or one of the other type, is `JSMN_ERROR_INVAL`; otherwise it is closed
at `pos + 1`, `toksuper = -1`, and the second search (`close_second_elim`, composed by
`lastOpen_close`) makes `toksuper` the open token below it; then `pos++`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop dflt isOpen lastOpen OBJECT ARRAY STRING
  PRIMITIVE ERROR_INVAL step_close_none step_close_some)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The token fields of a well-formed state are values of their C types. -/
theorem tokRange_of_wf {js : List Nat} {n : Nat} {st : St} (hwf : Jsmn.WF js n st)
    (hlen : js.length < 2 ^ 31) : TokRange st.toks := by
  intro t ht
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hwf.tok t ht
  simp only [OBJECT, ARRAY, STRING, PRIMITIVE] at h1
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem step_close (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 125 ∨ byteAt js st.pos = 93) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hL := hwf.len_n
  have hpos := hwf.pos_le
  have htp := hwf.len_pos
  have hrng := tokRange_of_wf hwf (by omega)
  have hlpos := hl.1
  have hc' := hc
  have htr : TokRange st.toks := hrng
  have hL0 : st.toks.length = 0 ∨ 0 < st.toks.length := by omega
  obtain ⟨tyv, htyv⟩ : ∃ tyv : Int, tyv = if byteAt js st.pos = 125 then 1 else 2 := ⟨_, rfl⟩
  have htyr : 0 ≤ tyv ∧ tyv ≤ 4294967295 := by rw [htyv]; split <;> decide
  rcases hc with hc | hc <;> rcases hL0 with h0 | h0
  all_goals
    have cirH_c := hc
    -- `i = toknext - 1` (the `unsigned` subtraction wraps at `toknext = 0`)
    have cirH_wm1 : wrap true 32 (wrap false 32 (-1)) = -1 := by decide
    (try have cirH_L : st.toks.length = 0 := h0)
    (try have cirH_L1 : (0 : Int) ≤ (st.toks.length : Int) - 1 := by omega)
    (try have cirH_L2 : (st.toks.length : Int) - 1 ≤ 2147483647 := by omega)
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    -- the first search
    obtain ⟨⟨st2, σ2⟩, hk, henv2, hnames2, hnx2, hfr2, hcase⟩ := close_first_elim (ts := st.toks) (n := n)
      (pos := st.pos) (sup := st.sup) (ty := tyv) (bp := bp) (bt := bt) (bPar := m.next + 1) (bTok := m.next + 4)
      (bI := m.next + 7) (bToken := m.next + 8) (bType := σ.mem.next + 1) (bRet := m.next) (kp := kp) (kt := kt)
      (vTk := v8) (vR := .undef) (f := m.next)
      hs (by simp only [upd]; exact e5) (by simp only [upd]; exact e6) (by simp only [upd]; exact e9)
      (by simp only [upd]; exact e12) (by simp only [upd]; exact e13) (by simp only [upd]; rfl)
      (by simp (disch := omega) only [upd_apply_ne]; exact l1) (by simp (disch := omega) only [upd_apply_ne]; exact l4)
      (by simp (disch := omega) only [upd_apply_ne, upd_apply_same]; try (rw [h0]; rfl))
      (by simp (disch := omega) only [upd_apply_ne]; exact l8)
      (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, htyv, hc, ↓reduceIte]; try rfl)
      (by simp (disch := omega) only [upd_apply_ne]; exact l0)
      (by simp (disch := omega) only [upd_apply_ne]; exact hpb)
      (by simp (disch := omega) only [upd_apply_ne]; exact htb)
      hkp hkt (by omega) (by omega) htyr htr rfl rfl rfl rfl rfl (by omega) hbpn hbtn hpt
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega)
    dsimp only at hk henv2 hnames2 hnx2 hfr2 hcase
    have cirH_env2 := henv2
    have cirH_names2 := hnames2
    have cirH_fr2 := hfr2
    cases hlo : lastOpen st.toks st.toks.length with
    | none =>
      -- no open token: `if (i == -1) return JSMN_ERROR_INVAL`
      rw [hlo] at hcase
      dsimp only at hcase
      obtain ⟨ha, cirH_i2, hp2, ht2, hr2', ⟨vt2, cirH_k2⟩⟩ := hcase
      subst ha
      have cirH_p2 : σ2.mem.blocks bp =
          some ⟨kp, true, .record "jsmn_parser", .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩ := by
        rw [hp2]; simp (disch := omega) only [upd_apply_ne]; exact hpb
      have cirH_t2 : σ2.mem.blocks bt =
          some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩ := by
        rw [ht2]; simp (disch := omega) only [upd_apply_ne]; exact htb
      have cirH_r2 : σ2.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
        rw [hr2']; simp (disch := omega) only [upd_apply_ne]; exact l0
      clear hp2 ht2 hr2'
      cir_hrun_c hk
      subst hk
      refine ⟨⟨ERROR_INVAL, step_close_none hc' hlo, rfl⟩, ⟨st.toks, hL, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
      · simp (disch := omega) only [killRange_of_lt, upd_apply_ne]; exact cirH_t2
      · simp (disch := omega) only [killRange_of_lt, upd_apply_ne]
        rw [cirH_fr2 b (by omega) (by omega) (by omega) h1 h2 (by omega)]
        simp (disch := omega) only [upd_apply_ne]
        exact hfr b hb h1 h2
      · dsimp only; omega
    | some k =>
      rw [hlo] at hcase
      dsimp only at hcase
      have hk1 : k < st.toks.length := lastOpen_lt _ _ _ hlo
      first
      | -- (`toknext = 0`: no open token)
        (exfalso; omega)
      | by_cases htype : (st.toks.getD k dflt).type = tyv
        · -- the bracket's type: closed at `pos + 1`; then the second search
          rw [if_pos htype] at hcase
          obtain ⟨ha, cirH_i2, hp2, ht2, hr2', ⟨vt2, cirH_k2⟩⟩ := hcase
          subst ha
          unfold parserV at hp2
          have cirH_p2 := hp2
          have cirH_t2 := ht2
          clear hp2 ht2
          have cirH_r2 : σ2.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
            rw [hr2']; simp (disch := omega) only [upd_apply_ne]; exact l0
          clear hr2'
          cir_hrun_c hk
          -- the second search, from `i = k`
          have hts' : (st.toks.set k { st.toks.getD k dflt with stop := (st.pos : Int) + 1 }).length =
              st.toks.length := List.length_set ..
          have htr' : TokRange (st.toks.set k { st.toks.getD k dflt with stop := (st.pos : Int) + 1 }) := by
            intro t ht
            rcases mem_set_or ht with h | h
            · exact htr t h
            · subst h
              have := htr _ (getD_mem hk1 dflt)
              dsimp only
              omega
          have hk1' : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
          obtain ⟨⟨st4, σ4⟩, hk4, ha4, henv4, hnames4, hnx4, hfr4, ⟨vi4, hi4⟩, ⟨vt4, htk4⟩, hp4⟩ :=
            close_second_elim (ts := st.toks.set k { st.toks.getD k dflt with stop := (st.pos : Int) + 1 })
            (n := n) (pos := st.pos) (sup := -1) (m0 := k + 1) (bp := bp) (bt := bt) (bPar := m.next + 1)
            (bTok := m.next + 4) (bI := m.next + 7) (bToken := m.next + 8) (kp := kp) (kt := kt)
            (vTk := vt2)
            hk (by simp only [upd]; exact e6) (by simp only [upd]; exact e9) (by simp only [upd]; exact e12)
            (by simp only [upd]; exact e13)
            (by simp (disch := omega) only [killRange_of_lt]
                rw [cirH_fr2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
                simp (disch := omega) only [upd_apply_ne]; exact l1)
            (by simp (disch := omega) only [killRange_of_lt]
                rw [cirH_fr2 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
                simp (disch := omega) only [upd_apply_ne]; exact l4)
            (by simp (disch := omega) only [killRange_of_lt]; rw [hk1']; exact cirH_i2)
            (by simp (disch := omega) only [killRange_of_lt]; exact cirH_k2)
            (by simp (disch := omega) only [killRange_of_lt]; rw [hts']; exact cirH_p2)
            (by simp (disch := omega) only [killRange_of_lt]; exact cirH_t2)
            hkp (by omega) (by omega) htr' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
            (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
          dsimp only at hk4 ha4 henv4 hnames4 hnx4 hfr4 hi4 htk4 hp4
          subst ha4
          rw [lastOpen_close st.toks k ((st.pos : Int) + 1) (by omega) hk1, hts'] at hp4
          have cirH_env4 := henv4
          have cirH_names4 := hnames4
          have cirH_fr4 := hfr4
          have cirH_i4 := hi4
          have cirH_tk4 := htk4
          unfold parserV at hp4
          have cirH_p4 := hp4
          clear hp4
          cir_hrun_c hk4
          subst hk4
          have hmatch : ¬ ((st.toks.getD k dflt).type ≠ if byteAt js st.pos = 125 then OBJECT else ARRAY) := by
            simp only [OBJECT, ARRAY]; rw [← htyv]; exact fun h => h htype
          have hstep : step js n st = .ok ⟨st.pos + 1,
              st.toks.set k { st.toks.getD k dflt with stop := st.pos + 1 },
              match lastOpen st.toks k with | some j => j | none => -1⟩ := by
            rw [step_close_some hc' hlo, if_neg hmatch]
            rfl
          have hpc : ((st.pos + 1 : Nat) : Int) = (st.pos : Int) + 1 := by omega
          refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_, fun b hb h1 h2 => ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨vi4, ?_⟩, ⟨vt4, ?_⟩, ?_, ?_, ?_⟩⟩
          all_goals (try (dsimp only [Mem.endScope]; omega))
          all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
            upd_apply_same, cirH_fr4, cirH_fr2, cirH_r2, cirH_i4, cirH_tk4, cirH_t2, l0, l1, l2, l3, l4, l5, l6, l9,
            hfr, List.length_set, hpc]; done))
          all_goals (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_same,
            List.length_set, hpc]
                     first | done | rfl)
        · -- another type: `return JSMN_ERROR_INVAL`
          rw [if_neg htype] at hcase
          obtain ⟨ha, hp2, ht2⟩ := hcase
          subst ha
          have cirH_t2 : σ2.mem.blocks bt =
              some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩ := by
            rw [ht2]; simp (disch := omega) only [upd_apply_ne]; exact htb
          clear hp2 ht2
          have hmis : (st.toks.getD k dflt).type ≠ if byteAt js st.pos = 125 then OBJECT else ARRAY := by
            simp only [OBJECT, ARRAY]; rw [← htyv]; exact htype
          have hstep : step js n st = .error ERROR_INVAL := by
            rw [step_close_some hc' hlo, if_pos hmis]
          dsimp only at hk
          cir_hrun_c hk
          subst hk
          refine ⟨⟨ERROR_INVAL, hstep, rfl⟩, ⟨st.toks, hL, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
          · simp (disch := omega) only [killRange_of_lt, upd_apply_ne]; exact cirH_t2
          · simp (disch := omega) only [killRange_of_lt, upd_apply_ne]
            rw [cirH_fr2 b (by omega) (by omega) (by omega) h1 h2 (by omega)]
            simp (disch := omega) only [upd_apply_ne]
            exact hfr b hb h1 h2
          · dsimp only; omega

end EquivLean.Demo.XLang.Jsmn.C
