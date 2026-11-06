import EquivLean.Demo.XLang.Jsmn.CPDefs
import EquivLean.Demo.XLang.Jsmn.CString

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on `"`

`step_quote`: one turn of the main loop on `"`: `jsmn_parse_string` (through its contract `parse_string_pspec`),
`return r` when it fails, else `count++`, the parent's `size++` when `toksuper != -1`, and `pos++`, per the model's
`step`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop incSize bumpSup dflt parseString STRING)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- `jsmn_parse_string`'s errors: `JSMN_ERROR_NOMEM`, `JSMN_ERROR_INVAL`, `JSMN_ERROR_PART`. -/
private theorem quote_err {js : List Nat} {n : Nat} {st : St} {e : Int}
    (h : parseString js n st = .error e) : e = -1 ∨ e = -2 ∨ e = -3 := by
  unfold parseString at h
  split at h
  · rename_i e' he
    cases h
    rcases Jsmn.strScan_err he with h | h <;> simp [h, Jsmn.ERROR_INVAL, Jsmn.ERROR_PART]
  · split at h
    · cases h; simp [Jsmn.ERROR_NOMEM]
    · cases h

private theorem quote_getD_mem {l : List Tok} {i : Nat} (h : i < l.length) : l.getD i dflt ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- The token array after `tokens[i].size++`, as the executor leaves it. -/
private theorem quote_tokArr_bump (xs : List Tok) (n i : Nat) (hi : i < xs.length) :
    (tokArr xs n).set i (.agg [.int (xs.getD i dflt).type, .int (xs.getD i dflt).start,
      .int (xs.getD i dflt).stop, .int ((xs.getD i dflt).size + 1)]) = tokArr (incSize xs i) n := by
  have e : incSize xs i = xs.set i { xs.getD i dflt with size := (xs.getD i dflt).size + 1 } := by
    unfold incSize
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      rw [List.getElem_modify, List.getElem_set]
      by_cases hik : i = k
      · subst hik
        rw [ite_eq_left rfl, ite_eq_left rfl, Jsmn.getD_of_lt hi]
      · rw [ite_eq_right hik, ite_eq_right hik]
  rw [e, ← tokArr_set xs n i _ hi]
  rfl

set_option hygiene false in
/-- Closes the memory goals of `step_quote` after the call: block counter, the caller's blocks, the locals, the
parser block, the token array, through the call's frame `cirH_fr2` and the loop head's facts. -/
macro "q_close" : tactic => `(tactic| (
  all_goals (try (dsimp only [Mem.endScope]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, cirH_fr2, cirH_tb2, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, hfr]; done))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq, incSize,
    List.length_modify, List.length_append, List.length_cons, List.length_nil, and_true, true_and]; omega))))

theorem step_quote (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 34) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hL := hwf.len_n
  have hpos := hwf.pos_le
  have hLp := hwf.len_pos
  have hsup := hwf.sup
  have cirH_c := hc
  cir_hrun_c hs
  try (simp only [evalOp] at hs; cir_hrun_c hs)
  -- `jsmn_parse_string(parser, js, len, tokens, num_tokens)`, by its contract
  obtain ⟨⟨ex, ma⟩, -, hpost, hs⟩ := holds_pspec_elim hs
    (parse_string_pspec js n st bp bj bt kp kj kt _ hjs hlen hn hL hl.1
    (by simp (disch := omega) only [upd_apply_ne, hpb]) hkp
    (by simp (disch := omega) only [upd_apply_ne, cirH_bj])
    (by simp (disch := omega) only [upd_apply_ne, htb]) hkt hpj hpt hjt
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega))
  obtain ⟨⟨ret, st', hm, hex, cirH_pb2, cirH_tb2⟩, cirH_fr2, cirH_nx2⟩ := hpost
  dsimp only at hex cirH_pb2 cirH_tb2 cirH_fr2 cirH_nx2
  subst hex
  rcases hps' : parseString js n st with e | s
  · -- the string is malformed or there is no token left: `return r`
    rw [hps'] at hm
    obtain ⟨rfl, hst⟩ := hm
    subst st'
    have herr := quote_err hps'
    have cirH_neg : ret < 0 := by omega
    have cirH_rg0 : -2147483648 ≤ ret := by omega
    have cirH_rg1 : ret ≤ 2147483647 := by omega
    have hstep : step js n st = .error ret := by
      rw [EquivLean.Demo.XLang.Jsmn.step_quote hc, hps']
    cir_hrun_c hs
    all_goals (
      subst hs
      refine ⟨⟨ret, hstep, rfl⟩, ⟨st.toks, hL, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
      · simp (disch := omega) only [Mem.endScope, upd_apply_ne, killRange_of_lt, cirH_tb2]
      · simp (disch := omega) only [Mem.endScope, upd_apply_ne, killRange_of_lt, cirH_fr2, hfr]
      · dsimp only [Mem.endScope]; omega)
  · rw [hps'] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨q, hq, hlt, rfl⟩ := Jsmn.parseString_ok hps'
    have hq1 := Jsmn.strScan_ge js (st.pos + 1) 0 hq
    have hq2 := Jsmn.strScan_lt js (st.pos + 1) 0 hq
    simp only [List.length_append, List.length_singleton] at cirH_pb2
    push_cast at cirH_pb2
    have cirH_cnt0 : -2147483648 ≤ (st.toks.length : Int) + 1 := by omega
    have cirH_cnt1 : (st.toks.length : Int) + 1 ≤ 2147483647 := by omega
    have cirH_q0 : (0 : Int) ≤ (q : Int) + 1 := by omega
    have cirH_q1 : (q : Int) + 1 ≤ 4294967295 := by omega
    rcases hsup with hs1 | ⟨hs1, hs2⟩
    · -- no parent
      have cirH_sup : st.sup = -1 := hs1
      have hstep : step js n st = .ok ⟨q + 1, st.toks ++ [⟨STRING, st.pos + 1, q, 0⟩], st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_quote hc, hps']
        simp [bumpSup, hs1]
      cir_hrun_c hs
      all_goals (
        subst hs
        refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨.int 0, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        q_close)
    · -- the parent `toksuper`: its size grows
      have cirH_sup : ¬ (st.sup = -1) := by omega
      have hi : st.sup.toNat < st.toks.length := by omega
      have cirH_si : st.sup.toNat < (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have cirH_tv : ∀ t : Tok, tokV t = .agg [.int t.type, .int t.start, .int t.stop, .int t.size] :=
        fun t => rfl
      have cirH_tg : ∀ i, i < (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]).length →
          (tokArr (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]) n)[i]? =
            some (tokV ((st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]).getD i dflt)) :=
        fun i h => tokArr_get_lt _ _ _ h
      have cirH_tl : (tokArr (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]) n).length = n :=
        tokArr_length _ _ (by simp only [List.length_append, List.length_singleton]; omega)
      have cirH_gs : (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]).getD st.sup.toNat dflt =
          st.toks.getD st.sup.toNat dflt := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have hsz := (hwf.tok _ (quote_getD_mem hi)).2.2.2.2.2
      have cirH_sz0 : -2147483648 ≤ (st.toks.getD st.sup.toNat dflt).size + 1 := by omega
      have cirH_sz1 : (st.toks.getD st.sup.toNat dflt).size + 1 ≤ 2147483647 := by omega
      have cirH_sti : ((st.sup.toNat : Nat) : Int) = st.sup := by omega
      have hstep : step js n st =
          .ok ⟨q + 1, incSize (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]) st.sup.toNat,
            st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_quote hc, hps']
        simp [bumpSup, cirH_sup]
      have htk := quote_tokArr_bump (st.toks ++ [(⟨STRING, (st.pos : Int) + 1, (q : Int), 0⟩ : Tok)]) n
        st.sup.toNat cirH_si
      rw [cirH_gs] at htk
      cir_hrun_c hs
      all_goals (
        subst hs
        refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨.int 0, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        q_close
        all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
          upd_apply_same, htk]; done)))

end EquivLean.Demo.XLang.Jsmn.C
