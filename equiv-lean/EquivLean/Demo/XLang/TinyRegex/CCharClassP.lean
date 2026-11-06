import EquivLean.Demo.XLang.TinyRegex.CCharClass
import EquivLean.Demo.XLang.TinyRegex.CPartial

/-!
# tiny-regex-c → model, C side: `matchcharclass` (partial correctness)

The `do`-`while` loop runs in the hypothesis (`holds_do_inv`): the invariant is that the class
positions passed did not match (`cclC xs c k = cclC xs c j` for the current position `j`).
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- `matchcharclass(c, &ccl_buf[k])` for a class string whose NUL is at `e`: if it returns,
it returns the C algorithm's result `cclC xs c k`. -/
theorem matchcharclass_pspec (xs : List Int) (bc k e : Nat) (c : Int) (kd : BlockKind) (tyc : Ty) (m : Mem)
    (hblk : m.blocks bc = some ⟨kd, true, tyc, .arr (xs.map .int)⟩)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) (hbc : bc < m.next)
    (hc : -128 ≤ c ∧ c ≤ 127) (hc0 : c ≠ 0) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hk1 : 1 ≤ k) (hke : k ≤ e) (he : e < xs.length) (he0 : xs.getD e 0 = 0) :
    pholds (evalCall ctx fn_matchcharclass.sym [.int c, .ptr (.loc bc [.idx k])] m)
      (fun r => ∃ v, r.1 = .ret (some (.int v)) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
        (v ≠ 0 ↔ cclC xs c k = true) ∧ (∀ b, b < m.next → r.2.blocks b = m.blocks b) ∧
        m.next ≤ r.2.next) := by
  obtain ⟨es, tlen, cirH_tyc⟩ := htyc
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_c := hc
  have cirH_t0 : ∀ n : Nat, ((n : Int) + 0).toNat = n := fun n => by omega
  have cirH_t1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  have cirH_g : ∀ (i : Nat) (h : i < xs.length), xs[i] = xs.getD i 0 := fun i h => getElem_eq_getD h
  have cirH_w8 : ∀ i, CIR.wrap true 8 (xs.getD i 0) = s8 (xs.getD i 0) := fun i => (s8_facts (getD_range hxs i)).1
  have cirH_w32 : ∀ i, CIR.wrap true 32 (s8 (xs.getD i 0)) = s8 (xs.getD i 0) := fun i =>
    (s8_facts (getD_range hxs i)).2.1
  have cirH_e0 : ∀ i, (s8 (xs.getD i 0) = 0) = (xs.getD i 0 = 0) := fun i => (s8_facts (getD_range hxs i)).2.2.2.1
  have cirH_e92 : ∀ i, (s8 (xs.getD i 0) = 92) = (xs.getD i 0 = 92) := fun i =>
    (s8_facts (getD_range hxs i)).2.2.2.2.2.1
  have cirH_e45 : ∀ i, (s8 (xs.getD i 0) = 45) = (xs.getD i 0 = 45) := fun i =>
    (s8_facts (getD_range hxs i)).2.2.2.2.1
  cir_hstep hs
  cir_hrun_c hs
  obtain ⟨s0, hs0, hs⟩ := holds_do_name hs
  refine (fun hw => ?main) (holds_do_inv hs
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ s0.mem.next ≤ σ.mem.next ∧
      (∀ b, b ≠ m.next + 2 → b < s0.mem.next → σ.mem.blocks b = s0.mem.blocks b) ∧
      ∃ (j : Nat), σ.mem.blocks (m.next + 2) =
          some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc bc [.idx j])⟩ ∧
        k ≤ j ∧ j ≤ e ∧ cclC xs c k = cclC xs c j)
    (fun a => s0.mem.next ≤ a.2.mem.next ∧
      ((∃ v, a.1 = .exit (.ret (some (.int v))) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
          (v ≠ 0 ↔ cclC xs c k = true) ∧ (∀ b, b < m.next → a.2.mem.blocks b = m.blocks b)) ∨
       (a.1 = .next ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧ cclC xs c k = false ∧
          (∀ b, b ≠ m.next + 2 → b < s0.mem.next → a.2.mem.blocks b = s0.mem.blocks b))))
    ?init ?step)
  case init =>
    subst hs0
    exact ⟨rfl, rfl, Nat.le_refl _, fun b _ _ => rfl, k, by simp only [upd_apply_same], Nat.le_refl _, hke, rfl⟩
  case step =>
    intro σ ⟨cirH_env, cirH_names, cirH_nx, cirH_frame, j, cirH_slot, hj1, hj2, hinv⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    have cirH_b2 : 1 ≤ j := by omega
    have b0 : xs.getD j 0 ≠ 0 → j < e := lt_of_getD_ne he0 hj2
    have b1 : xs.getD (j + 1) 0 ≠ 0 → j + 1 ≤ e → j + 1 < e := fun h h2 => lt_of_getD_ne he0 h2 h
    have cirH_r0 := getD_range hxs j
    have cirH_r1 := getD_range hxs (j + 1)
    subst hs0
    dsimp only at cirH_env cirH_names cirH_nx cirH_frame
    unfold doIter at hs2
    cir_hrun_c hs2
    -- `matchrange(c, str)`
    have cirH_blk : σ.mem.blocks bc = some ⟨kd, true, tyc, .arr (xs.map .int)⟩ := by
      rw [cirH_frame bc (by omega) (by omega)]; simp (disch := omega) only [upd_apply_ne, hblk]
    obtain ⟨v1, m1, -, hp1, hs2⟩ := holds_returns_elim hs2
      (matchrange_spec xs bc j c kd tyc σ.mem cirH_blk ⟨es, tlen, cirH_tyc⟩ (by omega) hc hxs (by omega)
        (fun _ h _ => by have := b0 h; omega)
        (fun _ h _ h2 => by have := b0 h; have := b1 (by omega) (by omega); omega))
    obtain ⟨⟨w1, cirH_v1, cirH_w1a, cirH_w1b, cirH_w1c⟩, cirH_fr1a, hfr1⟩ := hp1
    have cirH_fr1b := fun b hb => hfr1 b (List.not_mem_nil) hb
    clear hfr1
    subst cirH_v1
    have cirH_tm : ((j : Int) + -1).toNat = j - 1 := by omega
    have hs8j := s8_cases (xs.getD j 0)
    have hs8j1 := s8_cases (xs.getD (j + 1) 0)
    have hs8jm := s8_cases (xs.getD (j - 1) 0)
    have cirH_rm := getD_range hxs (j - 1)
    by_cases hw1 : w1 = 0
    · -- `matchrange` failed
      subst hw1
      have hnr : ¬ rangeP c xs j := fun h => absurd (cirH_w1c.2 h) (by omega)
      cir_hrun_c hs2
      all_goals (try subst hs2)
      all_goals first
        | (exfalso; omega)
        | (exfalso; simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; omega)
        | (simp only [Exit.cond.injEq, decide_eq_true_eq] at cirH_rd0; exact ⟨rfl, rfl, by dsimp only; omega,
            fun b hb1 hb2 => by
              dsimp only at hb2; simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_frame b hb1 hb2],
            j + 1, by simp only [upd_apply_same], by omega, by have := b0 cirH_rd0; omega,
            by rw [hinv]; exact cclC_next hnr (by omega) (by omega) (by omega) cirH_rd0⟩)
        | (simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; exact ⟨by dsimp only; omega,
            Or.inr ⟨rfl, rfl, rfl, by rw [hinv]; exact cclC_end hnr (by omega) (by omega) cirH_rd0,
            fun b hb1 hb2 => by
              dsimp only at hb2; simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_frame b hb1 hb2]⟩⟩)
        | (exact ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨1, rfl, by omega, by omega,
            ⟨fun _ => by
              rw [hinv]
              first
                | exact cclC_char hnr (by omega) (by omega) (by omega)
                | (rw [cclC_dash hnr (by omega) (by omega) (by omega)]; simp only [decide_eq_true_eq, Bool.or_eq_true]; omega),
              fun _ => by omega⟩,
            fun b hb => by
              simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr1b,
                cirH_frame b (by omega) (by omega)]⟩⟩)
        | (exact ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨_, rfl, by split <;> omega, by split <;> omega,
            by
              rw [hinv, cclC_dash hnr (by omega) (by omega) (by omega), Bool.or_eq_true, decide_eq_true_eq,
                decide_eq_true_eq]
              by_cases hz1 : xs.getD (j + 1) 0 = 0
              · rw [ite_eq_left hz1]; exact ⟨fun _ => Or.inr hz1, fun _ => by omega⟩
              · rw [ite_eq_right hz1]; exact ⟨fun h => absurd rfl h, fun h => by rcases h with h' | h' <;> omega⟩,
            fun b hb => by
              simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr1b,
                cirH_frame b (by omega) (by omega)]⟩⟩)
        | skip
      -- the escape `\\`: `str += 1; matchmetachar(c, str)`
      have h92 : xs.getD j 0 = 92 := by omega
      have hj1e : j + 1 ≤ e := by have := b0 (by omega); omega
      obtain ⟨v2, m2, -, hp2, hs2⟩ := holds_returns_elim hs2
        (matchmetachar_spec xs bc (j + 1) c kd tyc _
          (by simp (disch := omega) only [upd_apply_ne, cirH_fr1b, cirH_blk]) ⟨es, tlen, cirH_tyc⟩
          (by dsimp only; omega) hc hxs (by omega))
      obtain ⟨⟨w2, cirH_v2, cirH_w2a, cirH_w2b, cirH_w2c⟩, cirH_fr2a, hfr2⟩ := hp2
      have cirH_fr2b := fun b hb => hfr2 b (List.not_mem_nil) hb
      clear hfr2
      try dsimp only at cirH_fr2a cirH_fr2b
      subst cirH_v2
      by_cases hw2 : w2 = 0
      · subst hw2
        have hnm : ¬ metaP c (xs.getD (j + 1) 0) := fun h => absurd (cirH_w2c.2 h) (by omega)
        cir_hrun_c hs2
        all_goals (try subst hs2)
        all_goals first
          | (exfalso; simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; omega)
          | (simp only [Exit.cond.injEq, decide_eq_true_eq] at cirH_rd0; exact ⟨rfl, rfl, by dsimp only; omega,
              fun b hb1 hb2 => by
                dsimp only at hb2
                simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b, cirH_frame b hb1 hb2],
              j + 2, by simp only [upd_apply_same], by omega, by have := b1 cirH_rd0 hj1e; omega,
              by rw [hinv]; exact cclC_esc_next hnr h92 hnm (fun ⟨_, _⟩ => by omega) (by omega) cirH_rd0⟩)
          | (simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; exact ⟨by dsimp only; omega,
              Or.inr ⟨rfl, rfl, rfl, by rw [hinv]; exact cclC_esc_end hnr h92 hnm (fun ⟨_, _⟩ => by omega) cirH_rd0,
              fun b hb1 hb2 => by
                dsimp only at hb2
                simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b, cirH_frame b hb1 hb2]⟩⟩)
          | skip
        -- `(c == str[0]) && !ismetachar(c)`
        all_goals
          obtain ⟨v3, m3, -, hp3, hs2⟩ := holds_returns_elim hs2 (ismetachar_spec _ (by omega) _)
          obtain ⟨⟨w3, cirH_v3, cirH_w3a, cirH_w3b, cirH_w3c⟩, cirH_fr3a, hfr3⟩ := hp3
          have cirH_fr3b := fun b hb => hfr3 b (List.not_mem_nil) hb
          clear hfr3
          try dsimp only at cirH_fr3a cirH_fr3b
          rw [← cirH_br6] at cirH_w3c
          subst cirH_v3
          have hceq : c = s8 (xs.getD (j + 1) 0) := by omega
          by_cases hw3 : w3 = 0
          · subst hw3
            have hnmc : ¬ metacharP c := fun h => absurd (cirH_w3c.2 h) (by omega)
            cir_hrun_c hs2
            all_goals (try subst hs2)
            all_goals first
              | (exact ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨1, rfl, by omega, by omega,
                  ⟨fun _ => by rw [hinv]; exact cclC_esc hnr h92 hnm hceq hnmc, fun _ => by omega⟩,
                  fun b hb => by
                    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b,
                      cirH_fr3b, cirH_frame b (by omega) (by omega)]⟩⟩)
          · have hmc : metacharP c := cirH_w3c.1 hw3
            have cirH_w3t : (w3 != 0) = true := by simpa using hw3
            cir_hrun_c hs2
            all_goals (try subst hs2)
            all_goals first
              | (exfalso; simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; omega)
              | (simp only [Exit.cond.injEq, decide_eq_true_eq] at cirH_rd0; exact ⟨by rw [← cirH_br6], rfl,
                  by dsimp only; omega,
                  fun b hb1 hb2 => by
                    dsimp only at hb2
                    simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b, cirH_fr3b,
                      cirH_frame b hb1 hb2],
                  j + 2, by simp only [upd_apply_same], by omega, by have := b1 cirH_rd0 hj1e; omega,
                  by rw [hinv]; exact cclC_esc_next hnr h92 hnm (fun ⟨_, h2⟩ => h2 hmc) (by omega) cirH_rd0⟩)
              | (simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; exact ⟨by dsimp only; omega,
                  Or.inr ⟨rfl, rfl, rfl, by rw [hinv]; exact cclC_esc_end hnr h92 hnm (fun ⟨_, h2⟩ => h2 hmc) cirH_rd0,
                  fun b hb1 hb2 => by
                    dsimp only at hb2
                    simp (disch := omega) only [killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b, cirH_fr3b,
                      cirH_frame b hb1 hb2]⟩⟩)
      · have hm : metaP c (xs.getD (j + 1) 0) := cirH_w2c.1 hw2
        have cirH_w2t : (w2 != 0) = true := by simpa using hw2
        cir_hrun_c hs2
        all_goals (try subst hs2)
        all_goals first
          | (exact ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨1, rfl, by omega, by omega,
              ⟨fun _ => by rw [hinv]; exact cclC_meta hnr h92 hm, fun _ => by omega⟩,
              fun b hb => by
                simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr1b, cirH_fr2b,
                  cirH_frame b (by omega) (by omega)]⟩⟩)
    · -- `matchrange` matched: return 1
      have hr : rangeP c xs j := cirH_w1c.1 hw1
      have cirH_w1t : (w1 != 0) = true := by simpa using hw1
      cir_hrun_c hs2
      all_goals (try subst hs2)
      all_goals first
        | (exact ⟨by dsimp only [Mem.endScope]; omega, Or.inl ⟨1, rfl, by omega, by omega,
            ⟨fun _ => by rw [hinv]; exact cclC_range hr, fun _ => by omega⟩,
            fun b hb => by
              simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr1b,
                cirH_frame b (by omega) (by omega)]⟩⟩)
  case main =>
    obtain ⟨⟨st1, σ1⟩, ⟨hnx1, hpost⟩, hk1⟩ := hw
    subst hs0
    rcases hpost with ⟨v, hst1, hv1, hv2, hiff, hfr⟩ | ⟨hst1, cirH_env1, cirH_names1, hcf, cirH_fr⟩
    · -- returned from inside the loop
      dsimp only at hst1 hfr hnx1
      subst hst1
      cir_hrun_c hk1
      subst hk1
      exact ⟨v, rfl, hv1, hv2, hiff, fun b hb => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, hfr b hb],
        by dsimp only [Mem.endScope] at hnx1 ⊢; omega⟩
    · -- the loop ended: `return 0`
      dsimp only at hst1 cirH_env1 cirH_names1 cirH_fr hnx1
      subst hst1
      have cirH_rv : σ1.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
        rw [cirH_fr m.next (by omega) (by omega)]; simp (disch := omega) only [upd_apply_ne, upd_apply_same]
      cir_hrun_c hk1
      subst hk1
      exact ⟨0, rfl, by omega, by omega, by simp [hcf],
        fun b hb => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_fr b (by omega) (by omega)],
        by dsimp only [Mem.endScope] at hnx1 ⊢; omega⟩

end EquivLean.Demo.XLang.TinyRegex.C
