import EquivLean.Demo.XLang.Jsmn.CBase
import EquivLean.Demo.XLang.Jsmn.ModelStep

/-!
# jsmn → model, C side: the state of `jsmn_parse`'s main loop

The main loop's regions (`loopC`, `loopB`, `loopS`, taken from the generated module), and what a state at the
loop head holds for the model's parser state `st` (`PAt`): the alloca pointers in the environment, the locals
(`count = st.toks.length`), the parser block, the token array, the caller's other blocks. `StepPost`: what one turn
of the loop does per the model's `step` (an error return, or the next state). One lemma per byte class proves
`StepPost` (`CPStep*.lean`), from a state with the model's well-formedness `WF` (`ModelStep.lean`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx fn_jsmn_parse_ops9)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop)

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The condition region of `jsmn_parse`'s main loop. -/
def loopC : Region := match fn_jsmn_parse_ops9 with | [.forOp _ c _ _ _] => c | _ => ⟨[]⟩
/-- The body region of `jsmn_parse`'s main loop. -/
def loopB : Region := match fn_jsmn_parse_ops9 with | [.forOp _ _ b _ _] => b | _ => ⟨[]⟩
/-- The step region of `jsmn_parse`'s main loop (`parser->pos++`). -/
def loopS : Region := match fn_jsmn_parse_ops9 with | [.forOp _ _ _ s _] => s | _ => ⟨[]⟩

/-- A state at the head of `jsmn_parse`'s main loop holding the model's parser state `st`: the alloca pointers
(SSA values 5 .. 14, blocks `m.next ..`), the locals (`__retval`, `parser`, `js`, `len`, `tokens`, `num_tokens`, `r`,
`i`, `token`, `count = toknext`), the parser block, the token array, the caller's other blocks unchanged. -/
def PAt (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kt : BlockKind) (m : Mem) (st : St) (σ : State) : Prop :=
  σ.env 5 = some (.ptr (.loc m.next [])) ∧ σ.env 6 = some (.ptr (.loc (m.next + 1) [])) ∧
  σ.env 7 = some (.ptr (.loc (m.next + 2) [])) ∧ σ.env 8 = some (.ptr (.loc (m.next + 3) [])) ∧
  σ.env 9 = some (.ptr (.loc (m.next + 4) [])) ∧ σ.env 10 = some (.ptr (.loc (m.next + 5) [])) ∧
  σ.env 11 = some (.ptr (.loc (m.next + 6) [])) ∧ σ.env 12 = some (.ptr (.loc (m.next + 7) [])) ∧
  σ.env 13 = some (.ptr (.loc (m.next + 8) [])) ∧ σ.env 14 = some (.ptr (.loc (m.next + 9) [])) ∧
  σ.names = [("count", m.next + 9), ("token", m.next + 8), ("i", m.next + 7), ("r", m.next + 6),
    ("num_tokens", m.next + 5), ("tokens", m.next + 4), ("len", m.next + 3), ("js", m.next + 2),
    ("parser", m.next + 1), ("__retval", m.next)] ∧
  m.next + 10 ≤ σ.mem.next ∧
  (∀ b, b < m.next → b ≠ bp → b ≠ bt → σ.mem.blocks b = m.blocks b) ∧
  σ.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ ∧
  σ.mem.blocks (m.next + 1) = some ⟨.stack, true, (Ty.record "jsmn_parser").ptr, .ptr (.loc bp [])⟩ ∧
  σ.mem.blocks (m.next + 2) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bj [.idx 0])⟩ ∧
  σ.mem.blocks (m.next + 3) = some ⟨.stack, true, .int false 64, .int js.length⟩ ∧
  σ.mem.blocks (m.next + 4) = some ⟨.stack, true, (Ty.record "jsmntok").ptr, .ptr (.loc bt [.idx 0])⟩ ∧
  σ.mem.blocks (m.next + 5) = some ⟨.stack, true, .int false 32, .int n⟩ ∧
  (∃ v, σ.mem.blocks (m.next + 6) = some ⟨.stack, true, .int true 32, v⟩) ∧
  (∃ v, σ.mem.blocks (m.next + 7) = some ⟨.stack, true, .int true 32, v⟩) ∧
  (∃ v, σ.mem.blocks (m.next + 8) = some ⟨.stack, true, (Ty.record "jsmntok").ptr, v⟩) ∧
  σ.mem.blocks (m.next + 9) = some ⟨.stack, true, .int true 32, .int st.toks.length⟩ ∧
  σ.mem.blocks bp = some ⟨kp, true, .record "jsmn_parser", .agg [.int st.pos, .int st.toks.length, .int st.sup]⟩ ∧
  σ.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr st.toks n)⟩

/-- One turn of `jsmn_parse`'s main loop from a live position, per the model's `step`: either it returns the
model's error (the token array still an array of `n` records, the caller's other blocks unchanged), or the loop
goes on in the model's next state. -/
def StepPost (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kt : BlockKind) (m : Mem) (st : St) :
    (Step × State) ⊕ State → Prop
  | .inl o => (∃ e, step js n st = .error e ∧ o.1 = .exit (.ret (some (.int e)))) ∧
      (∃ ts : List Tok, ts.length ≤ n ∧
        o.2.mem.blocks bt = some ⟨kt, true, .array (.record "jsmntok") n, .arr (tokArr ts n)⟩) ∧
      (∀ b, b < m.next → b ≠ bp → b ≠ bt → o.2.mem.blocks b = m.blocks b) ∧ m.next + 10 ≤ o.2.mem.next
  | .inr σ' => ∃ st', step js n st = .ok st' ∧ PAt js n bp bj bt kp kt m st' σ'

set_option hygiene false in
/-- The start of a `StepPost` proof (after `intro r hr`): the facts of `hat : PAt …` and the text, named for the
executor (`cirH_…`), the loop test decided from `hl : live js st.pos`, and `hs`, the turn in the hypothesis. Expects
the lemma's hypotheses `hjs hbj hpj hpt hjt hbpn hbjn hbtn hkp hkt hat hl`. -/
macro "ps_intro" : tactic => `(tactic| (
  have hs := holds_of_eq_ok hr
  obtain ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, hnames, hnx, hfr, l0, l1, l2, l3, l4, l5, ⟨v6, l6⟩,
    ⟨v7, l7⟩, ⟨v8, l8⟩, l9, hpb, htb⟩ := hat
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
  have cirH_l8 := l8
  have cirH_l9 := l9
  have cirH_pb := hpb
  have cirH_tb := htb
  have cirH_bj : σ.mem.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩ := by rw [hfr bj hbjn (Ne.symm hpj) hjt]; exact hbj
  have cirH_kp := hkp
  have cirH_kt := hkt
  have cirH_pj := hpj
  have cirH_pt := hpt
  have cirH_jt := hjt
  have cirH_gd : ∀ (i : Nat) (h : i < js.length), js[i] = byteAt js i := fun i h => getElem_eq_byteAt h
  have cirH_ld := load_byte hjs
  have cirH_ld2 := load_byte2 hjs
  have cirH_w := wrap_byte hjs
  have cirH_z : ∀ x : Int, (0 : Int) + x = x := Int.zero_add
  have cirH_irm1 : inRange false 32 (-1) = false := by decide
  have hb0 := byteAt_lt hjs st.pos
  have cirH_sb0 : (0 : Int) ≤ (st.pos : Int) := by omega
  have cirH_sb1 : (st.pos : Int) ≤ (js.length : Int) := by have := hl.1; omega
  have cirH_c1 : (st.pos : Int) < (js.length : Int) := by have := hl.1; omega
  have cirH_c1' : st.pos < js.length := hl.1
  have cirH_c2 : ¬ ((byteAt js st.pos : Int) - 256 * ((byteAt js st.pos : Int) / 128) = 0) := by
    have := hl.2; omega
  unfold forIter at hs
  simp only [loopC, loopB, loopS, Gen.Cir.Jsmn.Jsmn.fn_jsmn_parse_ops9] at hs))

set_option hygiene false in
/-- Closes the memory goals of a `StepPost` proof: block counter, the caller's blocks, the locals, the token
array, block values up to `omega` on their integer fields (from the facts `ps_intro` named). -/
macro "ps_close" : tactic => `(tactic| (
  all_goals (try (dsimp only [Mem.endScope]; omega))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, htb, hfr]; done))
  all_goals (try (simp (disch := omega) only [Mem.endScope, killRange_self, killRange_of_lt, upd_apply_ne,
    upd_apply_same, Option.some.injEq, MemBlock.mk.injEq, Val.agg.injEq, List.cons.injEq, Val.int.injEq,
    List.length_append, List.length_cons, List.length_nil, and_true, true_and]; omega))))

end EquivLean.Demo.XLang.Jsmn.C
