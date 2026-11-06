import EquivLean.Demo.XLang.Jsmn.CPStepA
import EquivLean.Demo.XLang.Jsmn.CPStepDead
import EquivLean.Demo.XLang.Jsmn.CPStepOpen
import EquivLean.Demo.XLang.Jsmn.CPStepQuote
import EquivLean.Demo.XLang.Jsmn.CStepClose
import EquivLean.Demo.XLang.Jsmn.CStepComma
import EquivLean.Demo.XLang.Jsmn.CStepPrim
import EquivLean.Demo.XLang.Jsmn.CScan
import EquivLean.Demo.XLang.Jsmn.CModelFacts

/-!
# jsmn → model, C side: `jsmn_parse` (partial correctness)

`loop_step`: one turn of the main loop from a state holding a well-formed model state, by the byte class
(`CPStep*.lean`): the loop goes on in the model's next state (`LInv`), or ends: at a dead position with
`mainLoop`'s result, or with the model's error (`LPost`). `parse_pspec`: `jsmn_parse` from a parser state
`st0`: its return value and token array follow `mainLoop js n st0` and the final scan (`final_scan_elim`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop isOpen dflt)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The main loop's invariant: a well-formed model state, held by the state at the loop head, from which the
model's loop has the same outcome as from `st0`. -/
def LInv (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kt : BlockKind) (m : Mem) (st0 : St) (σ : State) :
    Prop :=
  ∃ st, Jsmn.WF js n st ∧ PAt js n bp bj bt kp kt m st σ ∧ mainLoop js n st0 = mainLoop js n st

/-- The main loop's outcomes: it ends at a dead position in a model state that is `mainLoop`'s result, or it
returns `mainLoop`'s error. -/
def LPost (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kt : BlockKind) (m : Mem) (st0 : St) (a : Step × State) :
    Prop :=
  (a.1 = .next ∧ ∃ st, Jsmn.WF js n st ∧ PAt js n bp bj bt kp kt m st a.2 ∧ ¬ live js st.pos ∧
    mainLoop js n st0 = .ok st) ∨
  ((∃ e, mainLoop js n st0 = .error e ∧ a.1 = .exit (.ret (some (.int e)))) ∧
    (∃ ts : List Tok, ts.length ≤ n ∧
      a.2.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩) ∧
    (∀ b, b < m.next → b ≠ bp → b ≠ bt → a.2.mem.blocks b = m.blocks b) ∧ m.next + 10 ≤ a.2.mem.next)

theorem mainLoop_live {js : List Nat} {n : Nat} {st : St} (hl : live js st.pos) :
    mainLoop js n st = (match step js n st with | .error e => .error e | .ok st' => mainLoop js n st') := by
  have h := Jsmn.mainLoop_eq js n st
  rw [if_pos hl] at h
  exact h

theorem mainLoop_dead {js : List Nat} {n : Nat} {st : St} (hl : ¬ live js st.pos) :
    mainLoop js n st = .ok st := by
  rw [Jsmn.mainLoop_eq, if_neg hl]

/-- One turn of `jsmn_parse`'s main loop, by the byte class at `pos`. -/
theorem loop_step (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st0 : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hinv : LInv js n bp bj bt kp kt m st0 σ) :
    pholds (forIter ctx loopC loopB loopS none σ) (fun r => match r with
      | .inl o => LPost js n bp bj bt kp kt m st0 o
      | .inr σ' => LInv js n bp bj bt kp kt m st0 σ') := by
  obtain ⟨st, hwf, hat, hml⟩ := hinv
  intro r hr
  by_cases hl : live js st.pos
  · have hsp : StepPost js n bp bj bt kp kt m st r := by
      by_cases c1 : byteAt js st.pos = 123 ∨ byteAt js st.pos = 91
      · exact step_open js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c1 r hr
      by_cases c2 : byteAt js st.pos = 125 ∨ byteAt js st.pos = 93
      · exact step_close js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c2 r hr
      by_cases c3 : byteAt js st.pos = 34
      · exact step_quote js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c3 r hr
      by_cases c4 : byteAt js st.pos = 9 ∨ byteAt js st.pos = 13 ∨ byteAt js st.pos = 10 ∨ byteAt js st.pos = 32
      · exact step_ws js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c4 r hr
      by_cases c5 : byteAt js st.pos = 58
      · exact step_colon js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c5 r hr
      by_cases c6 : byteAt js st.pos = 44
      · exact step_comma js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
          c6 r hr
      exact step_prim js n bp bj bt kp kj kt m st σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl
        (by omega) (by omega) (by omega) (by omega) c3 (by omega) (by omega) (by omega) (by omega) c5 c6 r hr
    cases r with
    | inl o =>
      obtain ⟨⟨e, he, ho⟩, hts, hfr, hnx⟩ := hsp
      exact Or.inr ⟨⟨e, by rw [hml, mainLoop_live hl, he], ho⟩, hts, hfr, hnx⟩
    | inr σ' =>
      obtain ⟨st', hst', hat'⟩ := hsp
      exact ⟨st', Jsmn.wf_step hst' hl hwf, hat', by rw [hml, mainLoop_live hl, hst']⟩
  · have hd := step_dead js n bp bj bt kp kj kt m st σ hjs hlen hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hwf hl r hr
    cases r with
    | inl o =>
      obtain ⟨ho, hat'⟩ := hd
      exact Or.inl ⟨ho, st, hwf, hat', hl, by rw [hml, mainLoop_dead hl]⟩
    | inr σ' => exact hd.elim

/-- The model's result of `jsmn_parse` from the parser state `st0` (`Model.parse` from `St.init`). -/
def pres (js : List Nat) (n : Nat) (st0 : St) : Int × List Tok :=
  match mainLoop js n st0 with
  | .error e => (e, [])
  | .ok st => if st.toks.any isOpen then (Jsmn.ERROR_PART, []) else (st.toks.length, st.toks)

theorem parse_eq_pres (js : List Nat) (n : Nat) : Jsmn.parse js n = pres js n St.init := rfl

theorem scan_start_wrap' (k : Nat) (hk : k < 2 ^ 31) :
    wrap true 32 (wrap false 32 ((k : Int) - 1)) = (k : Int) - 1 := by
  by_cases h0 : k = 0
  · subst h0; decide
  · rw [wrap_of_bounds (s := false) (w := 32) (x := (k : Int) - 1) (by decide)
      (by simp only [intMin_u, intMax_u32]; omega),
      wrap_of_bounds (s := true) (w := 32) (x := (k : Int) - 1) (by decide)
      (by simp only [intMin_s32, intMax_s32]; omega)]

set_option maxHeartbeats 2000000000 in
/-- **`jsmn_parse` per the model**, from a well-formed parser state `st0`: it returns the model's value
(`pres`: `mainLoop`'s error, or `JSMN_ERROR_PART` for an open token, or the token count) and leaves a token
array of `n` records starting with the model's tokens. -/
theorem parse_pspec (js : List Nat) (n : Nat) (st0 : St) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32) (hwf0 : Jsmn.WF js n st0)
    (hbp : m.blocks bp = some ⟨kp, true, .record "jsmn_parser",
      .agg [.int st0.pos, .int st0.toks.length, .int st0.sup]⟩) (hkp : kp ≠ .readonly)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hbt : m.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st0.toks n)⟩)
    (hkt : kt ≠ .readonly)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) :
    pholds (evalCall ctx "jsmn_parse"
        [.ptr (.loc bp []), .ptr (.loc bj [.idx 0]), .int js.length, .ptr (.loc bt [.idx 0]), .int n] m)
      (fun r => r.1 = .ret (some (.int (pres js n st0).1)) ∧
        (∃ ts : List Tok, ts.length ≤ n ∧
          r.2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩ ∧
          ((pres js n st0).2 = [] ∨ (pres js n st0).2 = ts)) ∧
        ∀ b, b < m.next → b ≠ bp → b ≠ bt → r.2.blocks b = m.blocks b) := by
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
  have hL0 := hwf0.len_n
  have cirH_tl : (tokArr st0.toks n).length = n := tokArr_length _ _ hL0
  have cirH_cw : wrap true 32 (st0.toks.length : Int) = (st0.toks.length : Int) :=
    wrap_of_bounds (by decide)
      (by simp only [intMin_s32, intMax_s32]; have := hwf0.len_pos; have := hwf0.pos_le; omega)
  cir_hstep hs
  cir_hrun_c hs
  obtain ⟨s0, hs00, hs0⟩ := holds_for_name hs
  refine (fun hw => ?main) (holds_for_inv hs0 (LInv js n bp bj bt kp kt m st0) (LPost js n bp bj bt kp kt m st0)
    ?init (fun σ hσ => loop_step js n bp bj bt kp kj kt m st0 σ hjs hlen hn hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt
      hσ))
  case init =>
    subst hs00
    refine ⟨st0, hwf0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, by dsimp only; omega, fun b hb h1 h2 => ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ⟨.undef, ?_⟩, ⟨.undef, ?_⟩, ⟨.undef, ?_⟩, ?_, ?_, ?_⟩, rfl⟩
    all_goals (try rfl)
    all_goals (simp (disch := omega) only [upd_apply_ne, upd_apply_same, cirH_bp, cirH_bt])
  case main =>
    obtain ⟨⟨st1, σ1⟩, hpost, hk1⟩ := hw
    rcases hpost with ⟨hst1, st, hwf, hat, hnl, hml⟩ | ⟨⟨e, hml, hst1⟩, ⟨ts, hts, hbt1⟩, hfr1, hnx1⟩
    · -- the loop ended: `if (tokens != NULL) { i = toknext - 1; the final scan }`, then `return count;`
      subst hs00
      dsimp only at hst1 hat
      subst hst1
      obtain ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, hnames, hnx, hfr, l0, l1, l2, l3, l4, l5, ⟨v6, l6⟩,
        ⟨v7, l7⟩, ⟨v8, l8⟩, l9, hpb, htb⟩ := hat
      have cirH_names := hnames
      have cirH_l0 := l0
      have cirH_l1 := l1
      have cirH_l4 := l4
      have cirH_l7 := l7
      have cirH_l9 := l9
      have cirH_pb := hpb
      have cirH_tb := htb
      have hL := hwf.len_n
      have hLp := hwf.len_pos
      have hpos := hwf.pos_le
      have cirH_ssw := scan_start_wrap' st.toks.length (by omega)
      have hrng : ∀ t ∈ st.toks, -2147483648 ≤ t.start ∧ t.start ≤ 2147483647 ∧ -2147483648 ≤ t.stop ∧
          t.stop ≤ 2147483647 := fun t ht => by have := hwf.tok t ht; omega
      cir_hrun_c hk1
      -- `i = toknext - 1` is in its slot (both signs of `toknext - 1` in `unsigned`): the final scan
      all_goals (
        obtain ⟨⟨a1, mem2, env2, names2⟩, hK, henv, hnm2, hnx2, hfr2, hcase⟩ := final_scan_elim st.toks n bt
          (m.next + 4) (m.next + 7) m.next kt .undef hk1 (by rfl) (by rfl) (by rfl)
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, l4])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, l0])
          (by simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, htb])
          (by omega) hrng (by omega) (by omega) (by omega) (by omega)
          (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
        dsimp only at henv hnm2 hnx2 hfr2 hcase hK
        subst henv hnm2
        have cirH_m9 : mem2.blocks (m.next + 9) = some ⟨.stack, true, .int true 32, .int (st.toks.length : Int)⟩ := by
          rw [hfr2 (m.next + 9) (by omega) (by omega) (by omega)]
          simp (disch := omega) only [upd_apply_ne, killRange_of_lt, l9]
        have cirH_mbt : mem2.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩ := by
          rw [hfr2 bt (by omega) (by omega) (by omega)]
          simp (disch := omega) only [upd_apply_ne, killRange_of_lt, htb]
        rcases hcase with ⟨hopen, ha1⟩ | ⟨hopen, ha1, hret⟩
        · -- an open token: `return JSMN_ERROR_PART`
          subst ha1
          have hpr : pres js n st0 = (Jsmn.ERROR_PART, []) := by unfold pres; rw [hml]; simp [hopen]
          cir_hrun_c hK
          all_goals (
            subst hK
            refine ⟨by rw [hpr]; try rfl, ⟨st.toks, hL, ?_, Or.inl (by rw [hpr])⟩, fun b hb h1 h2 => ?_⟩
            · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_mbt]
            · have h3 := hfr2 b (by omega) (by omega) (by omega)
              simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, h3,
                hfr b hb h1 h2])
        · -- none open: `return count`
          subst ha1
          have cirH_m0 : mem2.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
            rw [hret]; simp (disch := omega) only [upd_apply_ne, killRange_of_lt, l0]
          have hpr : pres js n st0 = ((st.toks.length : Int), st.toks) := by unfold pres; rw [hml]; simp [hopen]
          cir_hrun_c hK
          all_goals (
            subst hK
            refine ⟨by rw [hpr], ⟨st.toks, hL, ?_, Or.inr (by rw [hpr])⟩, fun b hb h1 h2 => ?_⟩
            · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_mbt]
            · have h3 := hfr2 b (by omega) (by omega) (by omega)
              simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, h3,
                hfr b hb h1 h2]))
    · -- `mainLoop`'s error: the return goes through
      subst hs00
      dsimp only at hst1 hbt1 hfr1 hnx1
      subst hst1
      cir_hrun_c hk1
      all_goals (
        subst hk1
        have hpr : pres js n st0 = (e, []) := by unfold pres; rw [hml]
        refine ⟨by rw [hpr], ⟨ts, hts, ?_, Or.inl (by rw [hpr])⟩, fun b hb h1 h2 => ?_⟩
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same, hbt1]
        · simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same,
            hfr1 b hb h1 h2])

end EquivLean.Demo.XLang.Jsmn.C
