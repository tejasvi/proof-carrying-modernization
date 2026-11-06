import EquivLean.Demo.XLang.Jsmn.CTok
import EquivLean.Demo.XLang.Jsmn.ModelLemmas

/-!
# jsmn → model, C side: `jsmn_parse_primitive`

`jsmn_parse_primitive_pspec`: `jsmn_parse_primitive(parser, js, len, tokens, n)` on a run's memory (the
parser `parserV st.pos st.toks.length st.sup`, the text `js` as bytes in a `char` block, the token
array `tokArr st.toks n`), from a position holding a live byte that is not a delimiter (as at its call
in `jsmn_parse`): every outcome follows the model's `parsePrimitive js n st`.  An error `e` returns
`e` and leaves the parser and the tokens as they were (`pos` is restored); `ok st'` returns 0 with
the parser and tokens of `st'`.

The scan `for (; parser->pos < len && js[parser->pos] != '\0'; parser->pos++)` runs in the
hypothesis by an invariant (`holds_for_inv`; the model's `primScan` from the current position
equals the one from the start); `goto found` and the loop's exit both reach the block labelled
`found`, entered with `holds_evalBlock_at_elim`; the two helper calls use `CTok`'s contracts.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (Tok St byteAt live primDelim primScan parsePrimitive PRIMITIVE
  ERROR_NOMEM ERROR_INVAL primScan_gt primScan_le)
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace EquivLean.Demo.XLang.Jsmn.C

/-- Entering block `i` of a region in a hypothesis (a `cir.br`, or a `goto` to a labelled block)
when `blocks[i]?` is known; `cir_hrun_c` enters block 0 only. -/
theorem holds_evalBlock_at_elim {ctx : Ctx} {blocks : List Block} {i : BlockId} {params : List VId}
    {ops : List Op} {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (hb : blocks[i]? = some (.mk params ops)) (h : (evalBlock ctx blocks i args σ).holds Q) :
    (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l blocks with
        | some j => evalBlock ctx blocks j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx blocks j vs σ
      | .next => .ub "fell off the end of a block").holds Q := by
  rw [evalBlock.eq_1, hb] at h; exact h

theorem primDelim_iff (c : Nat) :
    primDelim c = true ↔ (c = 58 ∨ c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32 ∨ c = 44 ∨ c = 93 ∨ c = 125) := by
  unfold primDelim; simp only [Bool.or_eq_true, beq_iff_eq]
  constructor <;> intro h <;> omega

/-- The `char` load of a byte, when the executor splits on its sign: the same linear value as
`load_byte`. -/
theorem wrap8_byte {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) :
    wrap true 8 ((byteAt js i : Nat) : Int) = (byteAt js i : Int) - 256 * ((byteAt js i : Int) / 128) := by
  have h := byteAt_lt hjs i
  unfold wrap
  have hp : (2 : Int) ^ 8 = 256 := by decide
  have hp7 : (2 : Int) ^ (8 - 1) = 128 := by decide
  simp only [hp, hp7, Bool.true_and, decide_eq_true_eq]
  have hm : ((byteAt js i : Nat) : Int) % 256 = (byteAt js i : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hm]
  split <;> omega

theorem wrap32_byte {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) :
    wrap true 32 ((byteAt js i : Nat) : Int) = (byteAt js i : Int) :=
  wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; have := byteAt_lt hjs i; omega)

theorem primDelim_false {c : Nat}
    (h : ¬ (c = 58 ∨ c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32 ∨ c = 44 ∨ c = 93 ∨ c = 125)) : primDelim c = false := by
  cases hc : primDelim c with
  | false => rfl
  | true => exact absurd ((primDelim_iff c).1 hc) h

/-- The scan stops at `p`: the end, a NUL, or a delimiter. -/
theorem primScan_stop {js : List Nat} {p : Nat} (h : ¬ live js p ∨ primDelim (byteAt js p) = true) :
    primScan js p = some p := by
  rw [primScan]
  by_cases hl : live js p
  · rw [dite_eq_left hl]; dsimp only
    rw [ite_eq_left (h.resolve_left (fun h' => h' hl))]
  · rw [dite_eq_right hl]

/-- A byte outside `32..126`: `JSMN_ERROR_INVAL`. -/
theorem primScan_bad {js : List Nat} {p : Nat} (hl : live js p) (hd : primDelim (byteAt js p) = false)
    (hb : byteAt js p < 32 ∨ 127 ≤ byteAt js p) : primScan js p = none := by
  rw [primScan, dite_eq_left hl]; dsimp only
  rw [ite_eq_right (by rw [hd]; decide), ite_eq_left hb]

/-- Any other byte: the scan goes on at `p + 1`. -/
theorem primScan_next {js : List Nat} {p : Nat} (hl : live js p) (hd : primDelim (byteAt js p) = false)
    (hb : ¬ (byteAt js p < 32 ∨ 127 ≤ byteAt js p)) : primScan js p = primScan js (p + 1) := by
  conv => lhs; rw [primScan, dite_eq_left hl]
  dsimp only
  rw [ite_eq_right (by rw [hd]; decide), ite_eq_right hb]

/-- **`jsmn_parse_primitive`** at `st.pos`, where `js[st.pos]` is a live byte and not a delimiter (as
at its call in `jsmn_parse`), on a run's memory: every outcome follows `parsePrimitive js n st`. -/
theorem jsmn_parse_primitive_pspec (js : List Nat) (n : Nat) (st : St) (m : Mem) (bp bj bt : Nat)
    (kp kj kt : BlockKind)
    (hp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV st.pos st.toks.length st.sup⟩)
    (hj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length, .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (ht : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩)
    (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly) (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 31) (hl : live js st.pos)
    (hd : primDelim (byteAt js st.pos) = false) (hn : st.toks.length ≤ n) (hn32 : n < 2 ^ 32)
    (hbp : bp < m.next) (hbj : bj < m.next) (hbt : bt < m.next) :
    pholds (evalCall ctx "jsmn_parse_primitive" [.ptr (.loc bp []), .ptr (.loc bj [.idx 0]), .int js.length,
        .ptr (.loc bt [.idx 0]), .int n] m)
      (fun a => m.next ≤ a.2.next ∧ (∀ b, b ≠ bp → b ≠ bt → b < m.next → a.2.blocks b = m.blocks b) ∧
        match parsePrimitive js n st with
        | .error e => a.1 = .ret (some (.int e)) ∧ a.2.blocks bp = m.blocks bp ∧ a.2.blocks bt = m.blocks bt
        | .ok st' => a.1 = .ret (some (.int 0)) ∧
          a.2.blocks bp = some ⟨kp, true, .record "jsmn_parser", parserV st'.pos st'.toks.length st'.sup⟩ ∧
          a.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st'.toks n)⟩) := by
  intro r hr
  let tyT : Ty := .array (.record "jsmntok") n
  let tyJ : Ty := .array (.int true 8) js.length
  have hs : (evalCall ctx "jsmn_parse_primitive" [.ptr (.loc bp []), .ptr (.loc bj [.idx 0]), .int js.length,
      .ptr (.loc bt [.idx 0]), .int n] m).holds (· = r) := by rw [hr]; rfl
  have hpos : st.pos < js.length := hl.1
  unfold parserV at hp
  have cirH_p := hp
  have cirH_j := hj
  have cirH_t := ht
  have cirH_kp := hkp
  have cirH_kt := hkt
  cir_hstep hs
  cir_hrun_c hs
  -- the scan `for (; parser->pos < len && js[parser->pos] != '\0'; parser->pos++)`
  obtain ⟨s0, hs0, hs⟩ := holds_for_name hs
  refine (fun hw => ?main) (holds_for_inv hs
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ s0.mem.next ≤ σ.mem.next ∧
      (∀ b, b ≠ bp → b < s0.mem.next → σ.mem.blocks b = s0.mem.blocks b) ∧
      ∃ p : Nat, st.pos ≤ p ∧ p ≤ js.length ∧
        σ.mem.blocks bp =
          some ⟨kp, true, .record "jsmn_parser", .agg [.int p, .int st.toks.length, .int st.sup]⟩ ∧
        primScan js p = primScan js st.pos)
    (fun a => a.2.env = s0.env ∧ a.2.names = s0.names ∧ s0.mem.next ≤ a.2.mem.next ∧
      (∀ b, b ≠ bp → b ≠ m.next → b < s0.mem.next → a.2.mem.blocks b = s0.mem.blocks b) ∧
      ((∃ q, primScan js st.pos = some q ∧ (a.1 = .next ∨ a.1 = .exit (.goto "found")) ∧
          a.2.mem.blocks bp =
            some ⟨kp, true, .record "jsmn_parser", .agg [.int q, .int st.toks.length, .int st.sup]⟩ ∧
          a.2.mem.blocks m.next = s0.mem.blocks m.next) ∨
        (primScan js st.pos = none ∧ a.1 = .exit (.ret (some (.int (-2)))) ∧
          a.2.mem.blocks bp =
            some ⟨kp, true, .record "jsmn_parser", .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩)))
    ?init ?step)
  case init =>
    subst hs0
    refine ⟨rfl, rfl, Nat.le_refl _, fun b _ _ => rfl, st.pos, Nat.le_refl _, by omega, ?_, rfl⟩
    simp (disch := omega) only [upd_apply_ne]
    exact hp
  case step =>
    intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, p, hp1, hp2, cirH_pp, hpe⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    subst hs0
    dsimp only at cirH_env cirH_names cirH_nx cirH_frame
    have cirH_i0 : (0 + (p : Int)).toNat = p := by omega
    have cirH_gb : ∀ h : p < js.length, js[p] = byteAt js p := fun h => getElem_eq_byteAt h
    have cirH_lb := load_byte hjs p
    have cirH_wb := wrap_byte hjs p
    have cirH_w8 := wrap8_byte hjs p
    have cirH_w32 := wrap32_byte hjs p
    have cirH_blt := byteAt_lt hjs p
    have hp1c : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by omega
    unfold forIter at hs2
    cir_hrun_c hs2
    all_goals (subst hs2; dsimp only)
    -- (the sub-goals are closed by `all_goals try`, not bullets: on some branches `refine` closes one
    -- of them by unification already)
    all_goals first
      | -- the scan stops at `p` (the end, a NUL or a delimiter): on to `found`
        (refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b h1 h2 h3 => ?_,
           Or.inl ⟨p, ?_, ?_, ?_, ?_⟩⟩
         all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                        exact cirH_frame b h1 h3)
         all_goals try (rw [← hpe]; exact primScan_stop (by rw [primDelim_iff]; unfold live; omega))
         all_goals try (first | exact Or.inl rfl | exact Or.inr rfl)
         all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne]); exact cirH_pp)
         all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_frame])
         done)
      | -- a byte outside 32..126: `JSMN_ERROR_INVAL`, `parser->pos = start`
        (refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b h1 h2 h3 => ?_, Or.inr ⟨?_, rfl, ?_⟩⟩
         all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                        exact cirH_frame b h1 h3)
         all_goals try (rw [← hpe]; exact primScan_bad (by unfold live; omega) (primDelim_false (by omega)) (by omega))
         all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])
         done)
      | -- the next byte: `parser->pos++`
        (refine ⟨rfl, rfl, by (try simp only [Mem.endScope]); omega, fun b h1 h3 => ?_, p + 1, by omega, by omega,
           ?_, ?_⟩
         all_goals try ((try simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne])
                        exact cirH_frame b h1 h3)
         all_goals try (simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_same, hp1c])
         all_goals try (rw [← hpe]
                        exact (primScan_next (by unfold live; omega) (primDelim_false (by omega)) (by omega)).symm)
         done)
  case main =>
    obtain ⟨⟨st1, σ1⟩, ⟨cirH_env1, cirH_names1, cirH_nx1, cirH_fr1, hcase⟩, hk1⟩ := hw
    subst hs0
    dsimp only at cirH_env1 cirH_names1 cirH_nx1 cirH_fr1 hcase hk1
    rcases hcase with ⟨q, hq, hst1, cirH_pq, cirH_mn⟩ | ⟨hq, hst1, cirH_pq⟩
    · -- `found`, by the end of the scan (`hst1 : st1 = .next`) or by `goto found`
      have hgt := primScan_gt hl hd hq
      have hqb := primScan_le js st.pos (by omega) hq
      have htl : (tokArr st.toks n).length = n := tokArr_length st.toks n hn
      rcases hst1 with hst1 | hst1 <;> subst hst1
      all_goals
        cir_hrun_c hk1
        try (replace hk1 := holds_evalBlock_at_elim (by rfl) hk1; cir_hrun_c hk1)
        -- `token = jsmn_alloc_token(parser, tokens, num_tokens)`
        have cirH_q1 : (bp : Nat) < σ1.mem.next := by omega
        obtain ⟨⟨e2, m2⟩, -, hp2, hk2⟩ := holds_pspec_elim hk1 (jsmn_alloc_token_pspec _ bp bt kp kt q
          st.toks.length st.sup n (tokArr st.toks n) .undef .undef .undef .undef
          (by simp (disch := omega) only [killRange_of_lt]; unfold parserV; exact cirH_pq)
          (by simp (disch := omega) only [killRange_of_lt, cirH_fr1, upd_apply_ne]; exact ht)
          hkp hkt hpt (by omega) hn32 (fun h => tokArr_get_next st.toks n h)
          (by dsimp only; omega) (by dsimp only; omega))
        obtain ⟨cirH_n2, cirH_f2, hc2⟩ := hp2
        dsimp only at cirH_n2 cirH_f2
        by_cases hc : n ≤ st.toks.length
        · -- `JSMN_ERROR_NOMEM`: `parser->pos = start`
          simp only [hc, ↓reduceIte] at hc2
          obtain ⟨he2, cirH_bp2, cirH_bt2⟩ := hc2
          subst he2
          cir_hrun_c hk2
          subst hk2
          simp only [parsePrimitive, hq, hc, ↓reduceIte, ERROR_NOMEM]
          refine ⟨by (try simp only [Mem.endScope]); omega, fun b h1 h2 h3 => ?_, trivial, ?_, ?_⟩
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f2, cirH_fr1]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
            exact hp.symm
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_bt2, cirH_fr1]
        · -- the token: `jsmn_fill_token(token, JSMN_PRIMITIVE, start, parser->pos)`, then `parser->pos--`
          simp only [hc, ↓reduceIte, parserV] at hc2
          obtain ⟨he2, cirH_bp2, cirH_bt2⟩ := hc2
          subst he2
          cir_hrun_c hk2
          obtain ⟨⟨e3, m3⟩, -, hp3, hk3⟩ := holds_pspec_elim hk2 (jsmn_fill_token_pspec _ bt st.toks.length kt
            n ((tokArr st.toks n).set st.toks.length (.agg [.undef, .int (-1), .int (-1), .int 0])) 8 st.pos q
            .undef (.int (-1)) (.int (-1)) (.int 0)
            (by simp (disch := omega) only [upd_apply_ne]; exact cirH_bt2) hkt
            (by simp [htl, show st.toks.length < n by omega]) (by dsimp only; omega))
          obtain ⟨he3, cirH_bt3, cirH_f3, cirH_n3⟩ := hp3
          dsimp only at cirH_bt3 cirH_f3 cirH_n3
          subst he3
          have hq1 : ((q - 1 : Nat) : Int) = (q : Int) - 1 := by omega
          cir_hrun_c hk3
          subst hk3
          simp only [parsePrimitive, hq, hc, ↓reduceIte]
          refine ⟨by (try simp only [Mem.endScope]); omega, fun b h1 h2 h3 => ?_, trivial, ?_, ?_⟩
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f3, cirH_f2, cirH_fr1]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, parserV, hq1,
              List.length_append, List.length_singleton]
          · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_bt3]
            rw [tokArr_alloc_fill st.toks n _ (by omega)]
            rfl
    · -- `JSMN_ERROR_INVAL`
      subst hst1
      cir_hrun_c hk1
      subst hk1
      simp only [parsePrimitive, hq, ERROR_INVAL]
      refine ⟨by (try simp only [Mem.endScope]); omega, fun b h1 h2 h3 => ?_, trivial, ?_, ?_⟩
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, cirH_fr1, upd_apply_ne]
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt]; rw [cirH_pq]; exact hp.symm
      · simp (disch := omega) only [Mem.endScope, killRange_of_lt, cirH_fr1, upd_apply_ne]

/-- `jsmn_parse_primitive_pspec` in the shape of `parse_string_pspec` (the return value and the state
`st'` after the call: `st` on an error, the model's state otherwise), on a run's blocks. -/
theorem jsmn_parse_primitive_out (js : List Nat) (n : Nat) (st : St) (m : Mem) (bp bj bt : Nat)
    (kp kj kt : BlockKind)
    (hp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩)
    (hj : m.blocks bj =
      some ⟨kj, true, .array (.int true 8) js.length, .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (ht : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩)
    (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly) (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt)
    (hbp : bp < m.next) (hbj : bj < m.next) (hbt : bt < m.next)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn31 : n < 2 ^ 31) (hn : st.toks.length ≤ n)
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
    hpt hjt hjs (by omega) hl hd hn (by omega) hbp hbj hbt r hr
  revert hpost
  cases parsePrimitive js n st with
  | error e =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨e, st, ⟨rfl, rfl⟩, h1, by rw [h2]; exact hp, by rw [h3]; exact ht, hfr, hnx⟩
  | ok s =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨0, s, ⟨rfl, rfl⟩, h1, h2, h3, hfr, hnx⟩

/-- At its call in `jsmn_parse` (the `default:` case of the switch on `c = js[pos]`), the byte is
none of the characters the switch handles, so not a delimiter of a primitive. -/
theorem primDelim_false_of_default {c : Nat}
    (h : c ≠ 123 ∧ c ≠ 91 ∧ c ≠ 125 ∧ c ≠ 93 ∧ c ≠ 34 ∧ c ≠ 9 ∧ c ≠ 13 ∧ c ≠ 10 ∧ c ≠ 32 ∧ c ≠ 58 ∧ c ≠ 44) :
    primDelim c = false :=
  primDelim_false (by omega)

end EquivLean.Demo.XLang.Jsmn.C
