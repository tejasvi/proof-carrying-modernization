import EquivLean.Demo.XLang.Jsmn.CPDefs

/-!
# jsmn → model, C side: `jsmn_parse`'s loop on whitespace and `:`

`step_ws`, `step_colon`: one turn of the main loop on `\t` `\r` `\n` ` ` (nothing but `pos++`) and on `:`
(`toksuper = toknext - 1`), per the model's `step`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

theorem step_ws (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St) (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 9 ∨ byteAt js st.pos = 13 ∨ byteAt js st.pos = 10 ∨ byteAt js st.pos = 32) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
    unfold step
    rcases hc with hc | hc | hc | hc <;> simp [hc]
  rcases hc with hc | hc | hc | hc
  all_goals (
    have cirH_c := hc
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    all_goals (
      subst hs
      refine ⟨⟨st.pos + 1, st.toks, st.sup⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, ?_,
        fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
      ps_close))

theorem step_colon (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28) (hn : n < 2 ^ 32)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hl : live js st.pos)
    (hc : byteAt js st.pos = 58) :
    pholds (forIter ctx loopC loopB loopS none σ) (StepPost js n bp bj bt kp kt m st) := by
  intro r hr
  ps_intro
  have hstep : step js n st = .ok ⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩ := by
    unfold step; simp [hc]
  have cirH_c := hc
  have hL : st.toks.length ≤ n := hwf.len_n
  have hLp := hwf.len_pos
  have hpos := hwf.pos_le
  by_cases h0 : st.toks.length = 0
  · have cirH_L : st.toks.length = 0 := h0
    have cirH_wm1 : wrap true 32 (wrap false 32 (-1)) = -1 := by decide
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    all_goals (
      subst hs
      refine ⟨⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13,
        e14, rfl, ?_, fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
      ps_close)
  · have cirH_L1 : (0 : Int) ≤ (st.toks.length : Int) - 1 := by omega
    have cirH_L2 : (st.toks.length : Int) - 1 ≤ 2147483647 := by omega
    cir_hrun_c hs
    try (simp only [evalOp] at hs; cir_hrun_c hs)
    all_goals (
      subst hs
      refine ⟨⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩, hstep, ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13,
        e14, rfl, ?_, fun b hb h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨v6, ?_⟩, ⟨v7, ?_⟩, ⟨v8, ?_⟩, ?_, ?_, ?_⟩⟩
      ps_close)

end EquivLean.Demo.XLang.Jsmn.C
