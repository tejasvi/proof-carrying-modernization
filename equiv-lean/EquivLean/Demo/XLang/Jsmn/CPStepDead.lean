import EquivLean.Demo.XLang.Jsmn.CPDefs

/-!
# jsmn → model, C side: `jsmn_parse`'s loop test fails

`step_dead`: at the end of the text or a NUL byte the main loop ends in the same state.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx)
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- The loop test fails (the end of the text, or a NUL byte): the loop ends in the same state. -/
theorem step_dead (js : List Nat) (n : Nat) (bp bj bt : Nat) (kp kj kt : BlockKind) (m : Mem) (st : St)
    (σ : State)
    (hjs : ∀ b ∈ js, b < 256) (hlen : js.length < 2 ^ 28)
    (hbj : m.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩)
    (hpj : bp ≠ bj) (hpt : bp ≠ bt) (hjt : bj ≠ bt) (hbpn : bp < m.next) (hbjn : bj < m.next)
    (hbtn : bt < m.next) (hkp : kp ≠ .readonly) (hkt : kt ≠ .readonly)
    (hat : PAt js n bp bj bt kp kt m st σ) (hwf : Jsmn.WF js n st) (hnl : ¬ live js st.pos) :
    pholds (forIter ctx loopC loopB loopS none σ) (fun r => match r with
      | .inl o => o.1 = .next ∧ PAt js n bp bj bt kp kt m st o.2
      | .inr _ => False) := by
  intro r hr
  have hs := holds_of_eq_ok hr
  have hat' := hat
  obtain ⟨e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, hnames, hnx, hfr, l0, l1, l2, l3, l4, l5, ⟨v6, l6⟩,
    ⟨v7, l7⟩, ⟨v8, l8⟩, l9, hpb, htb⟩ := hat
  have cirH_names := hnames
  have cirH_l1 := l1
  have cirH_l2 := l2
  have cirH_l3 := l3
  have cirH_pb := hpb
  have cirH_bj : σ.mem.blocks bj = some ⟨kj, true, .array (.int true 8) js.length,
      .arr (js.map fun b : Nat => Val.int (b : Int))⟩ := by rw [hfr bj hbjn (Ne.symm hpj) hjt]; exact hbj
  have cirH_pj := hpj
  have cirH_gd : ∀ (i : Nat) (h : i < js.length), js[i] = byteAt js i := fun i h => getElem_eq_byteAt h
  have cirH_ld := load_byte hjs
  have cirH_ld2 := load_byte2 hjs
  have cirH_w := wrap_byte hjs
  have cirH_z : ∀ x : Int, (0 : Int) + x = x := Int.zero_add
  have hb0 := byteAt_lt hjs st.pos
  have hpos := hwf.pos_le
  have cirH_sb0 : (0 : Int) ≤ (st.pos : Int) := by omega
  have cirH_sb1 : (st.pos : Int) ≤ (js.length : Int) := by omega
  unfold forIter at hs
  simp only [loopC, loopB, loopS, Gen.Cir.Jsmn.Jsmn.fn_jsmn_parse_ops9] at hs
  by_cases h1 : st.pos < js.length
  · have cirH_c1 : (st.pos : Int) < (js.length : Int) := by omega
    have cirH_c1' : st.pos < js.length := h1
    have cirH_c2 : byteAt js st.pos = 0 := by unfold live at hnl; omega
    cir_hrun_c hs
    all_goals (subst hs; exact ⟨rfl, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, hnx, hfr, l0, l1, l2, l3,
      l4, l5, ⟨v6, l6⟩, ⟨v7, l7⟩, ⟨v8, l8⟩, l9, hpb, htb⟩)
  · have cirH_c1 : ¬ ((st.pos : Int) < (js.length : Int)) := by omega
    have cirH_c1' : ¬ st.pos < js.length := h1
    cir_hrun_c hs
    all_goals (subst hs; exact ⟨rfl, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, rfl, hnx, hfr, l0, l1, l2, l3,
      l4, l5, ⟨v6, l6⟩, ⟨v7, l7⟩, ⟨v8, l8⟩, l9, hpb, htb⟩)

end EquivLean.Demo.XLang.Jsmn.C
