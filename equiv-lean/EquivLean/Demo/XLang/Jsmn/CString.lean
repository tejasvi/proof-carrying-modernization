import EquivLean.Demo.XLang.Jsmn.CStrSpec

/-!
# jsmn → model, C side: `jsmn_parse_string` (partial correctness)

`parse_string_pspec`: from the parser state `st` (`parser->pos` at the opening quote, the tokens `st.toks` in use,
`toknext = st.toks.length`), every outcome of `jsmn_parse_string(parser, js, len, tokens, n)` follows the model's
`parseString js n st` (`StrOut`): on an error `e` it returns `e` and leaves the state as it was; otherwise it returns
0 and leaves the model's new state (the string token, `pos` at the closing quote). No other block of the caller
changes. The loop runs in the hypothesis by an invariant (`holds_for_inv`; the `\uXXXX` digits by an inner one);
`jsmn_alloc_token` and `jsmn_fill_token` are inlined.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (strScan live byteAt escChar hexDigit ERROR_PART ERROR_INVAL ERROR_NOMEM STRING
  parseString St Tok)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The outcome of `jsmn_parse_string` per the model: the return value and the parser state left in the parser
and the token array, the other blocks of the caller unchanged. -/
def StrOut (js : List Nat) (n : Nat) (st : St) (bp bt : Nat) (kp kt : BlockKind) (m : Mem) (r : Exit × Mem) :
    Prop :=
  (∃ (ret : Int) (st' : St),
    (match parseString js n st with
      | .error e => ret = e ∧ st' = st
      | .ok s => ret = 0 ∧ st' = s) ∧
    r.1 = .ret (some (.int ret)) ∧
    r.2.blocks bp = some ⟨kp, true, .record "jsmn_parser",
      .agg [.int st'.pos, .int st'.toks.length, .int st'.sup]⟩ ∧
    r.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st'.toks n)⟩) ∧
  (∀ b, b < m.next → b ≠ bp → b ≠ bt → r.2.blocks b = m.blocks b) ∧ m.next ≤ r.2.next

/-- `jsmn_parse_string`'s locals at its loop head (blocks `m.next ..`): `__retval`, `parser`, `js`, `len`, `tokens`,
`num_tokens`, `token`, `start`. -/
abbrev SLoc (m sm : Mem) (bp bj bt len n start : Nat) : Prop :=
  sm.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ ∧
  sm.blocks (m.next + 1) = some ⟨.stack, true, (Ty.record "jsmn_parser").ptr, .ptr (.loc bp [])⟩ ∧
  sm.blocks (m.next + 2) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bj [.idx 0])⟩ ∧
  sm.blocks (m.next + 3) = some ⟨.stack, true, .int false 64, .int len⟩ ∧
  sm.blocks (m.next + 4) = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩ ∧
  sm.blocks (m.next + 5) = some ⟨.stack, true, .int false 64, .int n⟩ ∧
  sm.blocks (m.next + 6) = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .undef⟩ ∧
  sm.blocks (m.next + 7) = some ⟨.stack, true, .int true 32, .int start⟩

/-- `tokArr_push` with the token's record written out (as the executor leaves it). -/
theorem tokArr_push' (ts : List Tok) (n : Nat) (a b c d : Int) (h : ts.length < n) :
    (tokArr ts n).set ts.length (.agg [.int a, .int b, .int c, .int d]) = tokArr (ts ++ [⟨a, b, c, d⟩]) n :=
  tokArr_push ts n ⟨a, b, c, d⟩ h

set_option hygiene false in
/-- Closes the memory goals of `jsmn_parse_string`'s loop invariant and post (block counter, frame, locals, the
token array, block values up to `omega` on their integer fields), from the loop head's facts `l0 .. l7`, `htb`,
`hfr`. -/
macro "str_close" : tactic => `(tactic| (
  all_goals (try (dsimp only [Mem.endScope]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, l0, l1, l2, l3, l4, l5, l6, l7, htb, hfr]; done))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
    List.length_append, List.length_cons, List.length_nil, and_true, true_and]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, tokArr_push', STRING]; done))))

theorem parse_string_pspec (js : List Nat) (n : Nat) (st : St) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hts : st.toks.length ≤ n) (hst : st.pos < js.length)
    (hbp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser",
      .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩) (hkp : kp ≠ .readonly)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hbt : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩)
    (hkt : kt ≠ .readonly)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) :
    pholds (evalCall ctx "jsmn_parse_string"
        [.ptr (.loc bp []), .ptr (.loc bj [.idx 0]), .int js.length, .ptr (.loc bt [.idx 0]), .int n] m)
      (StrOut js n st bp bt kp kt m) := by
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_bp := hbp
  have cirH_bj := hbj
  have cirH_bt := hbt
  have cirH_kp := hkp
  have cirH_kt := hkt
  have cirH_pj := hpj
  have cirH_pt := hpt
  have cirH_jt := hjt
  have cirH_gd : ∀ (i : Nat) (h : i < js.length), js[i] = byteAt js i := fun i h => getElem_eq_byteAt h
  have cirH_ld := load_byte hjs
  have cirH_w := wrap_byte hjs
  have cirH_tl : (tokArr st.toks n).length = n := tokArr_length _ _ hts
  have cirH_z : ∀ x : Int, (0 : Int) + x = x := Int.zero_add
  cir_hstep hs
  cir_hrun_c hs
  obtain ⟨s0, hs00, hs0⟩ := holds_for_name hs
  refine (fun hw => ?main) (holds_for_inv hs0
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ m.next + 8 ≤ σ.mem.next ∧
      (∀ b, b < m.next → b ≠ bp → b ≠ bt → σ.mem.blocks b = m.blocks b) ∧
      SLoc m σ.mem bp bj bt js.length n st.pos ∧
      σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩ ∧
      ∃ q : Nat, σ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
          .agg [.int q, .int st.toks.length, .int st.sup]⟩ ∧
        st.pos + 1 ≤ q ∧ q ≤ js.length ∧ strScan js q 0 = strScan js (st.pos + 1) 0)
    (fun a => m.next ≤ a.2.mem.next ∧ (∀ b, b < m.next → b ≠ bp → b ≠ bt → a.2.mem.blocks b = m.blocks b) ∧
      ((a.1 = .next ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧ m.next + 8 ≤ a.2.mem.next ∧
        SLoc m a.2.mem bp bj bt js.length n st.pos ∧
        a.2.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩ ∧
        (∃ q : Nat, a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
          .agg [.int q, .int st.toks.length, .int st.sup]⟩) ∧
        strScan js (st.pos + 1) 0 = .error ERROR_PART) ∨
       (∃ (ret : Int) (st' : St),
        (match parseString js n st with
          | .error e => ret = e ∧ st' = st
          | .ok s => ret = 0 ∧ st' = s) ∧
        a.1 = .exit (.ret (some (.int ret))) ∧
        a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
          .agg [.int st'.pos, .int st'.toks.length, .int st'.sup]⟩ ∧
        a.2.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st'.toks n)⟩)))
    ?init ?step)
  case init =>
    subst hs00
    refine ⟨rfl, rfl, by dsimp only; omega, fun b hb h1 h2 => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
      st.pos + 1, ?_, by omega, by omega, rfl⟩
    all_goals (simp (disch := omega) only [upd_apply_ne, upd_apply_same, cirH_bt])
    all_goals (try (simp only [Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
      and_true, true_and]; omega))
  case step =>
    intro σ ⟨henv, hnames, hnx, hfr, ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩, htb, q, hpb, hq1, hq2, hscan⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    subst hs00
    unfold forIter at hs2
    have cirH_env := henv
    have cirH_names := hnames
    have cirH_fr := hfr
    have cirH_l0 := l0
    have cirH_l1 := l1
    have cirH_l2 := l2
    have cirH_l3 := l3
    have cirH_l4 := l4
    have cirH_l5 := l5
    have cirH_l6 := l6
    have cirH_l7 := l7
    have cirH_tb := htb
    have cirH_pb := hpb
    have hb0 := byteAt_lt hjs q
    have hb1 := byteAt_lt hjs (q + 1)
    have cirH_ld2 := load_byte2 hjs
    have cirH_sb0 : (0 : Int) ≤ (q : Int) := by omega
    have cirH_sb1 : (q : Int) ≤ (js.length : Int) := by omega
    by_cases hl : live js q
    · have cirH_c1 : (q : Int) < (js.length : Int) := by have := hl.1; omega
      have cirH_c1' : q < js.length := hl.1
      have cirH_c2 : ¬ ((byteAt js q : Int) - 256 * ((byteAt js q : Int) / 128) = 0) := by
        have := hl.2; omega
      by_cases h34 : byteAt js q = 34
      · -- the closing quote at `q`
        have cirH_c34 : byteAt js q = 34 := h34
        have hq : strScan js (st.pos + 1) 0 = .ok q := by rw [← hscan]; exact ss_quote js q hl h34
        by_cases hfull : n ≤ st.toks.length
        · -- no token left: `JSMN_ERROR_NOMEM`
          have cirH_full : (n : Int) ≤ (st.toks.length : Int) := by omega
          cir_hrun_c hs2
          cir_hstep hs2
          cir_hrun_c hs2
          all_goals (try (exfalso; omega))
          all_goals (
            subst hs2
            refine ⟨?_, fun b hb h1 h2 => ?_, Or.inr ⟨ERROR_NOMEM, st, ?_, rfl, ?_, ?_⟩⟩
            str_close
            all_goals (rw [ps_nomem js n st q hq hfull]; exact ⟨rfl, rfl⟩))
        · -- the string token
          have cirH_full : ¬ ((n : Int) ≤ (st.toks.length : Int)) := by omega
          have cirH_tn : (tokArr st.toks n)[st.toks.length]? = some tok0 := tokArr_get_next _ _ (by omega)
          have cirH_t0 : tok0 = .agg [.undef, .undef, .undef, .undef] := rfl
          have cirH_tb0 : (0 : Int) ≤ (st.toks.length : Int) := by omega
          have cirH_tb1 : (st.toks.length : Int) ≤ (n : Int) := by omega
          cir_hrun_c hs2
          cir_hstep hs2
          cir_hrun_c hs2
          cir_hstep hs2
          cir_hrun_c hs2
          all_goals (try (exfalso; omega))
          all_goals (
            subst hs2
            refine ⟨?_, fun b hb h1 h2 => ?_, Or.inr ⟨0, ⟨q, st.toks ++ [⟨STRING, st.pos + 1, q, 0⟩], st.sup⟩, ?_, rfl,
              ?_, ?_⟩⟩
            str_close
            all_goals (rw [ps_ok js n st q hq (by omega)]; exact ⟨rfl, rfl⟩))
      · have cirH_n34 : ¬ ((byteAt js q : Int) - 256 * ((byteAt js q : Int) / 128) = 34) := by omega
        by_cases h92 : byteAt js q = 92 ∧ q + 1 < js.length
        · -- a backslash, and a byte after it
          have cirH_c92 : byteAt js q = 92 := h92.1
          have hl1 : q + 1 < js.length := h92.2
          have cirH_c92b : (q : Int) + 1 < (js.length : Int) := by omega
          have cirH_sb2 : (q : Int) + 1 ≤ (js.length : Int) := by omega
          by_cases hesc : escChar (byteAt js (q + 1)) = true
          · -- `"` `/` `\` `b` `f` `r` `n` `t`: the loop goes on at `q + 2`
            have hv : byteAt js (q + 1) = 34 ∨ byteAt js (q + 1) = 47 ∨ byteAt js (q + 1) = 92 ∨
                byteAt js (q + 1) = 98 ∨ byteAt js (q + 1) = 102 ∨ byteAt js (q + 1) = 114 ∨
                byteAt js (q + 1) = 110 ∨ byteAt js (q + 1) = 116 := by
              unfold escChar at hesc; simp only [Bool.or_eq_true, beq_iff_eq] at hesc; omega
            rcases hv with hv | hv | hv | hv | hv | hv | hv | hv
            all_goals (
              have cirH_e := hv
              cir_hrun_c hs2
              all_goals (
                subst hs2
                refine ⟨rfl, rfl, ?_, fun b hb h1 h2 => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, q + 2, ?_, by omega,
                  by omega, ?_⟩
                str_close
                all_goals (rw [← hscan]; exact (ss_esc js q hl h92.1 hl1 hesc).symm)))
          · have hesc' : escChar (byteAt js (q + 1)) = false := by simpa using hesc
            by_cases hu : byteAt js (q + 1) = 117
            · -- `\u`: up to four hex digits from `q + 2` (an inner loop), then the loop goes on after them
              have cirH_cu : byteAt js (q + 1) = 117 := hu
              have cirH_sb3 : (0 : Int) ≤ (q : Int) + 1 := by omega
              have hsu : strScan js (st.pos + 1) 0 = strScan js (q + 2) 4 := by
                rw [← hscan]; exact ss_u js q hl h92.1 hl1 hu
              cir_hrun_c hs2
              obtain ⟨s1, hs1, hs2⟩ := holds_for_name hs2
              refine (fun hw' => ?umain) (holds_for_inv hs2
                (fun τ => τ.env = s1.env ∧ τ.names = s1.names ∧ σ.mem.next + 2 ≤ τ.mem.next ∧
                  (∀ b, b < σ.mem.next → b ≠ bp → τ.mem.blocks b = σ.mem.blocks b) ∧
                  τ.mem.blocks σ.mem.next = some ⟨.stack, true, .int true 8, .int 92⟩ ∧
                  ∃ k : Nat, τ.mem.blocks (σ.mem.next + 1) = some ⟨.stack, true, .int true 32, .int k⟩ ∧
                    τ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
                      .agg [.int ((q + 2 + k : Nat) : Int), .int st.toks.length, .int st.sup]⟩ ∧
                    k ≤ 4 ∧ q + 2 + k ≤ js.length ∧ strScan js (q + 2) 4 = strScan js (q + 2 + k) (4 - k))
                (fun a => σ.mem.next + 2 ≤ a.2.mem.next ∧
                  ((a.1 = .next ∧ (∀ b, b < σ.mem.next → b ≠ bp → a.2.mem.blocks b = σ.mem.blocks b) ∧
                    a.2.env = s1.env ∧ a.2.names = s1.names ∧
                    a.2.mem.blocks σ.mem.next = some ⟨.stack, true, .int true 8, .int 92⟩ ∧
                    ∃ k : Nat, a.2.mem.blocks (σ.mem.next + 1) = some ⟨.stack, true, .int true 32, .int k⟩ ∧
                      a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
                        .agg [.int ((q + 2 + k : Nat) : Int), .int st.toks.length, .int st.sup]⟩ ∧
                      k ≤ 4 ∧ q + 2 + k ≤ js.length ∧ ¬ (k < 4 ∧ live js (q + 2 + k)) ∧
                      strScan js (q + 2) 4 = strScan js (q + 2 + k) (4 - k)) ∨
                   (a.1 = .exit (.ret (some (.int (-2)))) ∧
                    (∀ b, b < m.next → b ≠ bp → a.2.mem.blocks b = σ.mem.blocks b) ∧
                    a.2.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser",
                      .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩ ∧
                    strScan js (q + 2) 4 = .error ERROR_INVAL)))
                ?uinit ?ustep)
              case uinit =>
                subst hs1
                refine ⟨rfl, rfl, by dsimp only; omega, fun b hb h1 => ?_, ?_, 0, ?_, ?_, by omega, by omega, rfl⟩
                all_goals (try (simp (disch := omega) only [upd_apply_ne, upd_apply_same]; done))
                all_goals (simp (disch := omega) only [upd_apply_ne, upd_apply_same, Option.some.injEq,
                  MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq, and_true, true_and]; omega)
              case ustep =>
                intro τ ⟨henvu, hnamesu, hnxu, hfru, hcu, k, hiu, hpbu, hk4, hkl, hscu⟩ r3 hr3
                have hs3 := holds_of_eq_ok hr3
                subst hs1
                unfold forIter at hs3
                have cirH_envu := henvu
                have cirH_namesu := hnamesu
                have cirH_fru := hfru
                have cirH_cu' := hcu
                have cirH_iu := hiu
                have cirH_pbu := hpbu
                have hbk := byteAt_lt hjs (q + (2 + k))
                have hqk : q + 2 + k = q + (2 + k) := by omega
                rw [hqk] at hpbu hscu
                have cirH_pbu := hpbu
                have cirH_ub0 : (0 : Int) ≤ ((q + (2 + k) : Nat) : Int) := by omega
                have cirH_ub1 : ((q + (2 + k) : Nat) : Int) ≤ (js.length : Int) := by omega
                by_cases hlu : k < 4 ∧ live js (q + (2 + k))
                · have cirH_k4 : (k : Int) < 4 := by omega
                  have cirH_u1 : ((q + (2 + k) : Nat) : Int) < (js.length : Int) := by have := hlu.2.1; omega
                  have cirH_u1' : q + (2 + k) < js.length := hlu.2.1
                  have cirH_u2 : ¬ ((byteAt js (q + (2 + k)) : Int) -
                      256 * ((byteAt js (q + (2 + k)) : Int) / 128) = 0) := by
                    have := hlu.2.2; omega
                  by_cases hx : hexDigit (byteAt js (q + (2 + k))) = true
                  · -- a hex digit: the inner loop goes on with `k + 1` digits read
                    have hx' : (48 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 57) ∨
                        (65 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 70) ∨
                        (97 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 102) := by
                      unfold hexDigit at hx; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
                      omega
                    revert hx'
                    cir_hrun_c hs3
                    all_goals intro hx'
                    all_goals (try (exfalso; (try simp only [decide_eq_false_iff_not, decide_eq_true_eq] at *); omega))
                    all_goals (subst hs3)
                    all_goals (
                      refine ⟨?env, rfl, ?_, fun b hb h1 => ?_, ?_, k + 1, ?_, ?_, by omega, by omega, ?_⟩
                      case env => rfl
                      all_goals (try (dsimp only [Mem.endScope]; omega))
                      all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, hfru, hcu]; done))
                      all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                        List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                      rw [hscu, show q + 2 + (k + 1) = q + (2 + k) + 1 by omega,
                        show 4 - (k + 1) = 4 - k - 1 by omega]
                      exact ss_hex js (q + (2 + k)) (4 - k) hlu.2 (by omega) hx)
                  · -- not a hex digit: `JSMN_ERROR_INVAL`
                    have hx0 : hexDigit (byteAt js (q + (2 + k))) = false := by simpa using hx
                    have hx' : ¬ ((48 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 57) ∨
                        (65 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 70) ∨
                        (97 ≤ byteAt js (q + (2 + k)) ∧ byteAt js (q + (2 + k)) ≤ 102)) := by
                      unfold hexDigit at hx; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
                      omega
                    revert hx'
                    cir_hrun_c hs3
                    all_goals intro hx'
                    all_goals (try (exfalso; (try simp only [decide_eq_false_iff_not, decide_eq_true_eq] at *); omega))
                    all_goals (subst hs3)
                    all_goals (
                      refine ⟨?_, Or.inr ⟨rfl, fun b hb h1 => ?_, ?_, ?_⟩⟩
                      all_goals (try (dsimp only [Mem.endScope]; omega))
                      all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, hfru, hcu]; done))
                      all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                        List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                      rw [hscu]
                      exact ss_nonhex js (q + (2 + k)) (4 - k) hlu.2 (by omega) hx0)
                · -- the inner loop ends: four digits read, or the end of the text, or a NUL byte
                  have hexit : ¬ (k < 4 ∧ live js (q + (2 + k))) := hlu
                  by_cases hk4' : k < 4
                  · have cirH_k4 : (k : Int) < 4 := by omega
                    by_cases hlen' : q + (2 + k) < js.length
                    · have cirH_u1 : ((q + (2 + k) : Nat) : Int) < (js.length : Int) := by omega
                      have cirH_u1' : q + (2 + k) < js.length := hlen'
                      have cirH_u0 : byteAt js (q + (2 + k)) = 0 := by unfold live at hlu; omega
                      cir_hrun_c hs3
                      all_goals (
                        subst hs3
                        refine ⟨?_, Or.inl ⟨rfl, fun b hb h1 => ?_, rfl, rfl, ?_, k, ?_, ?_, by omega, by omega,
                          by rw [hqk]; exact hexit, by rw [hqk]; exact hscu⟩⟩
                        all_goals (try (dsimp only [Mem.endScope]; omega))
                        all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                          upd_apply_ne, upd_apply_same, hfru, hcu, hiu]; done))
                        all_goals (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                          upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                          List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                    · have cirH_u1 : ¬ (((q + (2 + k) : Nat) : Int) < (js.length : Int)) := by omega
                      have cirH_u1' : ¬ q + (2 + k) < js.length := hlen'
                      cir_hrun_c hs3
                      all_goals (
                        subst hs3
                        refine ⟨?_, Or.inl ⟨rfl, fun b hb h1 => ?_, rfl, rfl, ?_, k, ?_, ?_, by omega, by omega,
                          by rw [hqk]; exact hexit, by rw [hqk]; exact hscu⟩⟩
                        all_goals (try (dsimp only [Mem.endScope]; omega))
                        all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                          upd_apply_ne, upd_apply_same, hfru, hcu, hiu]; done))
                        all_goals (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                          upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                          List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                  · have cirH_k4 : ¬ ((k : Int) < 4) := by omega
                    cir_hrun_c hs3
                    all_goals (
                      subst hs3
                      refine ⟨?_, Or.inl ⟨rfl, fun b hb h1 => ?_, rfl, rfl, ?_, k, ?_, ?_, by omega, by omega,
                        by rw [hqk]; exact hexit, by rw [hqk]; exact hscu⟩⟩
                      all_goals (try (dsimp only [Mem.endScope]; omega))
                      all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, hfru, hcu, hiu]; done))
                      all_goals (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                        upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                        List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
              case umain =>
                obtain ⟨⟨st2, τ2⟩, ⟨hnx2, hpost2⟩, hk2⟩ := hw'
                rcases hpost2 with ⟨hst2, hfr2, henv2, hnames2, hc2, k, hi2, hpb2, hk4, hkl, hexit, hsc2⟩ |
                  ⟨hst2, hfr2, hpb2, hinv2⟩
                · -- the digits are read: `parser->pos--`, then the loop goes on at `q + 2 + k`
                  subst hs1
                  dsimp only at hst2 henv2 hnames2 hc2 hi2 hpb2 hfr2 hnx2
                  subst hst2
                  have cirH_env2 := henv2
                  have cirH_names2 := hnames2
                  have cirH_fr2 := hfr2
                  have cirH_c2' := hc2
                  have cirH_i2 := hi2
                  have cirH_pb2 := hpb2
                  have cirH_pd : (0 : Int) ≤ ((q + 2 + k : Nat) : Int) - 1 := by omega
                  cir_hrun_c hk2
                  all_goals (
                    subst hk2
                    refine ⟨rfl, rfl, ?_, fun b hb h1 h2 => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, q + 2 + k, ?_,
                      by omega, by omega, ?_⟩
                    all_goals (try (dsimp only [Mem.endScope]; omega))
                    all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                      upd_apply_ne, upd_apply_same, hfr2, l0, l1, l2, l3, l4, l5, l6, l7, htb, hfr]; done))
                    all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                      upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                      List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                    rw [← hscan, ss_u js q hl h92.1 hl1 hu, hsc2]
                    by_cases hk4'' : k < 4
                    · have hd : ¬ live js (q + 2 + k) := fun h => hexit ⟨hk4'', h⟩
                      rw [ss_dead js _ _ hd, ss_dead js _ _ hd]
                    · rw [show 4 - k = 0 by omega])
                · -- a byte that is not a hex digit: `JSMN_ERROR_INVAL`
                  subst hs1
                  dsimp only at hst2 hpb2 hfr2 hnx2
                  subst hst2
                  have cirH_fr2 := hfr2
                  have cirH_pb2 := hpb2
                  cir_hrun_c hk2
                  all_goals (
                    subst hk2
                    refine ⟨?_, fun b hb h1 h2 => ?_, Or.inr ⟨ERROR_INVAL, st, ?_, rfl, ?_, ?_⟩⟩
                    all_goals (try (dsimp only [Mem.endScope]; omega))
                    all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                      upd_apply_ne, upd_apply_same, hfr2, l0, l1, l2, l3, l4, l5, l6, l7, htb, hfr]; done))
                    all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt,
                      upd_apply_ne, upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq,
                      List.cons.injEq, Val.int.injEq, and_true, true_and]; omega))
                    rw [ps_err js n st _ (by rw [hsu]; exact hinv2)]
                    exact ⟨rfl, rfl⟩)
            · -- any other byte after the backslash: `JSMN_ERROR_INVAL`
              have hne : byteAt js (q + 1) ≠ 34 ∧ byteAt js (q + 1) ≠ 47 ∧ byteAt js (q + 1) ≠ 92 ∧
                  byteAt js (q + 1) ≠ 98 ∧ byteAt js (q + 1) ≠ 102 ∧ byteAt js (q + 1) ≠ 114 ∧
                  byteAt js (q + 1) ≠ 110 ∧ byteAt js (q + 1) ≠ 116 := by
                unfold escChar at hesc'
                simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hesc'
                omega
              have cirH_x34 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 34) := by
                omega
              have cirH_x47 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 47) := by
                omega
              have cirH_x92 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 92) := by
                omega
              have cirH_x98 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 98) := by
                omega
              have cirH_x102 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 102) := by
                omega
              have cirH_x114 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 114) := by
                omega
              have cirH_x110 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 110) := by
                omega
              have cirH_x116 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 116) := by
                omega
              have cirH_x117 : ¬ ((byteAt js (q + 1) : Int) - 256 * ((byteAt js (q + 1) : Int) / 128) = 117) := by
                omega
              have hinv : strScan js (st.pos + 1) 0 = .error ERROR_INVAL := by
                rw [← hscan]; exact ss_bad js q hl h92.1 hl1 hesc' hu
              cir_hrun_c hs2
              all_goals (
                subst hs2
                refine ⟨?_, fun b hb h1 h2 => ?_, Or.inr ⟨ERROR_INVAL, st, ?_, rfl, ?_, ?_⟩⟩
                str_close
                all_goals (rw [ps_err js n st _ hinv]; exact ⟨rfl, rfl⟩))
        · -- another byte: the loop goes on at `q + 1`
          have cirH_n92 : ¬ ((byteAt js q : Int) - 256 * ((byteAt js q : Int) / 128) = 92 ∧
              (q : Int) + 1 < (js.length : Int)) := by omega
          cir_hrun_c hs2
          all_goals (try (exfalso; omega))
          all_goals (
            subst hs2
            refine ⟨rfl, rfl, ?_, fun b hb h1 h2 => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, q + 1, ?_, by omega,
              by omega, ?_⟩
            str_close
            all_goals (rw [← hscan]; exact (ss_other js q hl h34 (by omega)).symm))
    · -- the loop ends: the end of the text or a NUL byte
      by_cases h1 : q < js.length
      · have cirH_c1 : (q : Int) < (js.length : Int) := by omega
        have cirH_c1' : q < js.length := h1
        have cirH_z0 : byteAt js q = 0 := by unfold live at hl; omega
        cir_hrun_c hs2
        all_goals (
          subst hs2
          refine ⟨?_, fun b hb h1 h2 => ?_, Or.inl ⟨rfl, rfl, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨q, ?_⟩,
            ?_⟩⟩
          str_close
          all_goals (rw [← hscan]; exact ss_dead js q 0 hl))
      · have cirH_c1 : ¬ ((q : Int) < (js.length : Int)) := by omega
        have cirH_c1' : ¬ q < js.length := h1
        cir_hrun_c hs2
        all_goals (
          subst hs2
          refine ⟨?_, fun b hb h1 h2 => ?_, Or.inl ⟨rfl, rfl, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨q, ?_⟩,
            ?_⟩⟩
          str_close
          all_goals (rw [← hscan]; exact ss_dead js q 0 hl))
  case main =>
    obtain ⟨⟨st1, σ1⟩, ⟨hnx1, hfr1, hpost⟩, hk1⟩ := hw
    rcases hpost with ⟨hst1, henv1, hnames1, hnx1', ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩, htb1, ⟨q1, hpb1⟩, hpart⟩ |
      ⟨ret, st', hmatch, hst1, hpb1, htb1⟩
    · -- after the loop: `parser->pos = start; return JSMN_ERROR_PART;`
      subst hs00
      dsimp only at hst1 henv1 hnames1 hnx1' l0 l1 l2 l3 l4 l5 l6 l7 htb1 hpb1 hfr1 hnx1
      subst hst1
      have cirH_env1 := henv1
      have cirH_names1 := hnames1
      have cirH_l0 := l0
      have cirH_l1 := l1
      have cirH_l2 := l2
      have cirH_l3 := l3
      have cirH_l4 := l4
      have cirH_l5 := l5
      have cirH_l6 := l6
      have cirH_l7 := l7
      have cirH_tb1 := htb1
      have cirH_pb1 := hpb1
      cir_hrun_c hk1
      subst hk1
      refine ⟨⟨ERROR_PART, st, ?_, rfl, ?_, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
      · rw [ps_err js n st _ hpart]; exact ⟨rfl, rfl⟩
      all_goals (try (dsimp only [Mem.endScope]; omega))
      all_goals (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, htb1,
        hfr1])
    · subst hs00
      dsimp only at hst1 hpb1 htb1 hfr1 hnx1
      subst hst1
      cir_hrun_c hk1
      subst hk1
      refine ⟨⟨ret, st', hmatch, rfl, ?_, ?_⟩, fun b hb h1 h2 => ?_, ?_⟩
      all_goals (try (dsimp only [Mem.endScope]; omega))
      all_goals (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, hpb1,
        htb1, hfr1])

end EquivLean.Demo.XLang.Jsmn.C
