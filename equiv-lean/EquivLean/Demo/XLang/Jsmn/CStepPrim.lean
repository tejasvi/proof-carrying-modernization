import EquivLean.Demo.XLang.Jsmn.CPLemmas
import EquivLean.Demo.XLang.Jsmn.CPrim

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on the bytes of a primitive

`step_prim`: one turn of the main loop on a byte that none of the switch's cases takes (`default:`):
`jsmn_parse_primitive` (through its contract `jsmn_parse_primitive_pspec`), `return r` when it fails, else
`count++`, the parent's `size++` when `toksuper != -1`, and `pos++`, per the model's `step`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop incSize bumpSup dflt parsePrimitive primScan
  primDelim PRIMITIVE)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- `jsmn_parse_primitive_out` for every `n < 2^32`. -/
private theorem prim_out (js : List Nat) (n : Nat) (st : St) (m : Mem) (bp bj bt : Nat)
    (kp kj kt : BlockKind)
    (hp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩)
    (hj : m.blocks bj =
      some ⟨kj, true, .array (.int true 8) js.length, .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (ht : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩)
    (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly) (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt)
    (hbp : bp < m.next) (hbj : bj < m.next) (hbt : bt < m.next)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn32 : n < 2 ^ 32) (hn : st.toks.length ≤ n)
    (hl : live js st.pos) (hd : primDelim (byteAt js st.pos) = false) :
    pholds (evalCall ctx "jsmn_parse_primitive" [.ptr (.loc bp []), .ptr (.loc bj [.idx 0]), .int js.length,
        .ptr (.loc bt [.idx 0]), .int n] m)
      (fun r => ∃ (ret : Int) (st' : St),
        (match parsePrimitive js n st with
          | .error e => ret = e ∧ st' = st
          | .ok s => ret = 0 ∧ st' = s) ∧
        r.1 = .ret (some (.int ret)) ∧
        r.2.blocks bp =
          some ⟨kp, true, .record "jsmn_parser", .agg [.int st'.pos, .int st'.toks.length, .int st'.sup]⟩ ∧
        r.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st'.toks n)⟩ ∧
        (∀ b, b ≠ bp → b ≠ bt → b < m.next → r.2.blocks b = m.blocks b) ∧ m.next ≤ r.2.next) := by
  intro r hr
  obtain ⟨hnx, hfr, hpost⟩ := jsmn_parse_primitive_pspec js n st m bp bj bt kp kj kt hp hj ht hkp hkt hpj
    hpt hjt hjs (by omega) hl hd hn hn32 hbp hbj hbt r hr
  revert hpost
  cases parsePrimitive js n st with
  | error e =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨e, st, ⟨rfl, rfl⟩, h1, by rw [h2]; exact hp, by rw [h3]; exact ht, hfr, hnx⟩
  | ok s =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨0, s, ⟨rfl, rfl⟩, h1, h2, h3, hfr, hnx⟩

/-- `jsmn_parse_primitive`'s errors: `JSMN_ERROR_NOMEM`, `JSMN_ERROR_INVAL`. -/
private theorem prim_err {js : List Nat} {n : Nat} {st : St} {e : Int}
    (h : parsePrimitive js n st = .error e) : e = -1 ∨ e = -2 := by
  unfold parsePrimitive at h
  split at h
  · cases h; simp [Jsmn.ERROR_INVAL]
  · split at h
    · cases h; simp [Jsmn.ERROR_NOMEM]
    · cases h

/-- `jsmn_parse_primitive`'s result: the token `[pos, e)` with `pos = e - 1`, `e` the end of the scan. -/
private theorem prim_ok {js : List Nat} {n : Nat} {st : St} {s : St}
    (h : parsePrimitive js n st = .ok s) :
    ∃ e, primScan js st.pos = some e ∧ st.toks.length < n ∧
      s = ⟨e - 1, st.toks ++ [⟨PRIMITIVE, st.pos, e, 0⟩], st.sup⟩ := by
  unfold parsePrimitive at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · cases h
    · rename_i hn
      cases h
      exact ⟨e, he, by omega, rfl⟩

/-- The token array after `tokens[i].size++`, as the executor leaves it. -/
private theorem prim_tokArr_bump (xs : List Tok) (n i : Nat) (hi : i < xs.length) :
    (tokArr xs n).set i (.agg [.int (xs.getD i dflt).type, .int (xs.getD i dflt).start,
      .int (xs.getD i dflt).stop, .int ((xs.getD i dflt).size + 1)]) = tokArr (incSize xs i) n := by
  rw [incSize_eq, ← tokArr_set xs n i _ hi]
  rfl

set_option hygiene false in
/-- Closes the memory goals of `step_prim` after the call: block counter, the caller's blocks, the locals, the
parser block, the token array, through the call's frame `cirH_fr2` and the loop head's facts. -/
macro "pr_close" : tactic => `(tactic| (
  all_goals (try (dsimp only [Mem.endScope]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, cirH_fr2, cirH_tb2, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, hfr]; done))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq, incSize,
    List.length_modify, List.length_append, List.length_cons, List.length_nil, and_true, true_and]; omega))))

set_option maxHeartbeats 2000000000 in
theorem step_prim (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (h1 : byteAt js st.pos ≠ 123) (h2 : byteAt js st.pos ≠ 91) (h3 : byteAt js st.pos ≠ 125)
    (h4 : byteAt js st.pos ≠ 93) (h5 : byteAt js st.pos ≠ 34) (h6 : byteAt js st.pos ≠ 9)
    (h7 : byteAt js st.pos ≠ 13) (h8 : byteAt js st.pos ≠ 10) (h9 : byteAt js st.pos ≠ 32)
    (h10 : byteAt js st.pos ≠ 58) (h11 : byteAt js st.pos ≠ 44) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hL := hwf.len_n
  have hpos := hwf.pos_le
  have hLp := hwf.len_pos
  have hsup := hwf.sup
  have cirH_d1 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 123) := by omega
  have cirH_d2 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 91) := by omega
  have cirH_d3 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 125) := by omega
  have cirH_d4 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 93) := by omega
  have cirH_d5 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 34) := by omega
  have cirH_d6 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 9) := by omega
  have cirH_d7 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 13) := by omega
  have cirH_d8 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 10) := by omega
  have cirH_d9 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 32) := by omega
  have cirH_d10 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 58) := by omega
  have cirH_d11 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 44) := by omega
  have hd : primDelim (byteAt js st.pos) = false :=
    primDelim_false_of_default ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  cir_hrun_c hs
  try (simp only [evalOp] at hs; cir_hrun_c hs)
  -- `jsmn_parse_primitive(parser, js, len, tokens, num_tokens)`, by its contract
  obtain ⟨⟨ex, ma⟩, -, hpost, hs⟩ := holds_pspec_elim hs
    (prim_out js n st _ bp bj bt kp kj kt
      (by simp (disch := omega) only [upd_apply_ne, hpb])
      (by simp (disch := omega) only [upd_apply_ne, cirH_bj])
      (by simp (disch := omega) only [upd_apply_ne, htb]) hkp hkt hpj hpt hjt
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) hjs hlen hn hL hl hd)
  obtain ⟨ret, st', hm, hex, cirH_pb2, cirH_tb2, cirH_fr2, cirH_nx2⟩ := hpost
  dsimp only at hex cirH_pb2 cirH_tb2 cirH_fr2 cirH_nx2
  subst hex
  rcases hpp : parsePrimitive js n st with e | s
  · -- a byte outside 32..126, or no token left: `return r`
    rw [hpp] at hm
    obtain ⟨rfl, hst⟩ := hm
    subst st'
    have herr := prim_err hpp
    have cirH_neg : ret < 0 := by omega
    have cirH_rg0 : -2147483648 ≤ ret := by omega
    have cirH_rg1 : ret ≤ 2147483647 := by omega
    have hstep : step js n st = .error ret := by
      rw [EquivLean.Demo.XLang.Jsmn.step_prim h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, hpp]
    cir_hrun_c hs
    all_goals (
      subst hs
      refine ⟨⟨ret, hstep, rfl⟩, ⟨st.toks, hL, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
      · simp (disch := omega) only [Mem.endScope, upd_apply_ne, killRange_of_lt, cirH_tb2]
      · simp (disch := omega) only [Mem.endScope, upd_apply_ne, killRange_of_lt, cirH_fr2, hfr]
      · dsimp only [Mem.endScope]; omega)
  · rw [hpp] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨e, he, hlt, rfl⟩ := prim_ok hpp
    have he1 := Jsmn.primScan_gt hl hd he
    have he2 := Jsmn.primScan_le js st.pos hpos he
    have hce : (((e - 1 : Nat) : Int)) = (e : Int) - 1 := by omega
    simp only [List.length_append, List.length_singleton, hce] at cirH_pb2
    push_cast at cirH_pb2
    have cirH_cnt0 : -2147483648 ≤ (st.toks.length : Int) + 1 := by omega
    have cirH_cnt1 : (st.toks.length : Int) + 1 ≤ 2147483647 := by omega
    have cirH_q0 : (0 : Int) ≤ (e : Int) - 1 + 1 := by omega
    have cirH_q1 : (e : Int) - 1 + 1 ≤ 4294967295 := by omega
    rcases hsup with hs1 | ⟨hs1, hs2⟩
    · -- no parent
      have cirH_sup : st.sup = -1 := hs1
      have hstep : step js n st = .ok ⟨e, st.toks ++ [⟨PRIMITIVE, st.pos, e, 0⟩], st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_prim h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, hpp]
        simp only [bumpSup, hs1, ite_true, Except.ok.injEq, St.mk.injEq, and_true]
        omega
      cir_hrun_c hs
      all_goals (
        subst hs
        refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨.int 0, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        pr_close)
    · -- the parent `toksuper`: its size grows
      have cirH_sup : ¬ (st.sup = -1) := by omega
      have hi : st.sup.toNat < st.toks.length := by omega
      have cirH_si : st.sup.toNat < (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have cirH_tv : ∀ t : Tok, tokV t = .agg [.int t.type, .int t.start, .int t.stop, .int t.size] :=
        fun t => rfl
      have cirH_tg : ∀ i, i < (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]).length →
          (tokArr (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]) n)[i]? =
            some (tokV ((st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]).getD i dflt)) :=
        fun i h => tokArr_get_lt _ _ _ h
      have cirH_tl : (tokArr (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]) n).length = n :=
        tokArr_length _ _ (by simp only [List.length_append, List.length_singleton]; omega)
      have cirH_gs : (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]).getD st.sup.toNat dflt =
          st.toks.getD st.sup.toNat dflt := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have hsz := (hwf.tok _ (getD_mem hi dflt)).2.2.2.2.2
      have cirH_sz0 : -2147483648 ≤ (st.toks.getD st.sup.toNat dflt).size + 1 := by omega
      have cirH_sz1 : (st.toks.getD st.sup.toNat dflt).size + 1 ≤ 2147483647 := by omega
      have cirH_sti : ((st.sup.toNat : Nat) : Int) = st.sup := by omega
      have hstep : step js n st =
          .ok ⟨e, incSize (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]) st.sup.toNat,
            st.sup⟩ := by
        rw [EquivLean.Demo.XLang.Jsmn.step_prim h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, hpp]
        simp only [bumpSup, cirH_sup, ite_false, Except.ok.injEq, St.mk.injEq, and_true]
        omega
      have htk := prim_tokArr_bump (st.toks ++ [(⟨PRIMITIVE, (st.pos : Int), (e : Int), 0⟩ : Tok)]) n
        st.sup.toNat cirH_si
      rw [cirH_gs] at htk
      cir_hrun_c hs
      all_goals (
        subst hs
        refine ⟨_, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
          fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨.int 0, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
        pr_close
        all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
          upd_apply_same, htk]; done)))

end EquivLean.Demo.XLang.Jsmn.C
