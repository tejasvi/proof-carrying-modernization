import EquivLean.Demo.XLang.TinyRegex.CCharClassP
import EquivLean.Demo.XLang.TinyRegex.CCharClassModel
import EquivLean.Demo.XLang.TinyRegex.CBridge
import EquivLean.Demo.XLang.TinyRegex.CText

/-!
# tiny-regex-c → model, C side: `matchone` on the class tokens (partial correctness)

`matchone(p, c)` for a `CHAR_CLASS` (8) or `INV_CHAR_CLASS` (9) token: its union holds `u.ccl`,
a pointer to `ccl_buf[k]` (block 24), and the call is `matchcharclass(c, p.u.ccl)`, negated for 9.
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- `matchone(p, c)` for a class token whose class string at `ccl_buf[k]` has its NUL at `e`: if it
returns, it returns the C class test `cclC`, negated for `INV_CHAR_CLASS`. -/
theorem matchone_cls_pspec (xs : List Int) (ty k e : Nat) (c : Int) (kd : BlockKind) (tyc : Ty) (m : Mem)
    (hblk : m.blocks 24 = some ⟨kd, true, tyc, .arr (xs.map .int)⟩)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) (hn : 26 ≤ m.next)
    (hc : -128 ≤ c ∧ c ≤ 127) (hc0 : c ≠ 0) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hty : ty = 8 ∨ ty = 9) (hk1 : 1 ≤ k) (hke : k ≤ e) (he : e < xs.length) (he0 : xs.getD e 0 = 0) :
    pholds (evalCall ctx "matchone" [.agg [.int ty, .agg [.undef, .ptr (.loc 24 [.idx k])]], .int c] m)
      (fun r => ∃ v, r.1 = .ret (some (.int v)) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
        (v ≠ 0 ↔ (if ty = 8 then cclC xs c k else !cclC xs c k) = true) ∧
        (∀ b, b < m.next → r.2.blocks b = m.blocks b) ∧ m.next ≤ r.2.next) := by
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_c := hc
  rcases hty with rfl | rfl
  all_goals
    cir_hstep hs
    cir_hrun_c hs
    obtain ⟨⟨e1, m1⟩, -, hp1, hs⟩ := holds_pspec_elim hs
      (matchcharclass_pspec xs 24 k e c kd tyc _ (by simp (disch := omega) only [upd_apply_ne, hblk]) htyc
        (by dsimp only; omega) hc hc0 hxs hk1 hke he he0)
    obtain ⟨v, he1, hv1, hv2, hiff, cirH_f1, cirH_n1⟩ := hp1
    dsimp only at he1 cirH_f1 cirH_n1
    subst he1
    cir_hrun_c hs
    all_goals (try subst hs)
    first
      | exact ⟨v, rfl, hv1, hv2, by rw [ite_eq_left rfl]; exact hiff,
          fun b hb => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1],
          by dsimp only [Mem.endScope]; omega⟩
      | exact ⟨_, rfl, by split <;> omega, by split <;> omega,
          by
            have h98 : ¬ ((9 : Nat) = 8) := by decide
            rw [ite_eq_right h98]
            by_cases hv : v = 0
            · have hb1 : (v != 0) = false := by simp [hv]
              have hcf : cclC xs c k = false := by
                cases h : cclC xs c k
                · rfl
                · exact absurd (hiff.2 h) (fun h' => h' hv)
              rw [ite_eq_left hb1, hcf]
              exact ⟨fun _ => rfl, fun _ => by omega⟩
            · have hb1 : ¬ (v != 0) = false := by simp [hv]
              rw [ite_eq_right hb1, hiff.1 hv]
              exact ⟨fun h => absurd rfl h, fun h => absurd h (by decide)⟩,
          fun b hb => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_f1],
          by dsimp only [Mem.endScope]; omega⟩

/-- A token as `re_compile` leaves it: its fields are bytes, and a class token's string in
`ccl_buf` starts at index 1 or later and ends with a NUL inside the buffer. -/
def TokOK (B : Array Nat) (tok : Tok) : Prop :=
  tok.type < 256 ∧ tok.ch < 256 ∧
    ((tok.type = 8 ∨ tok.type = 9) → 1 ≤ tok.ccl ∧ ∃ e, tok.ccl ≤ e ∧ e < B.size ∧ B[e]! = 0)

/-- `matchone(p, c)` for any token as `re_compile` leaves it, against the model's `matchone` on the
byte `b` of `c`: if it returns, the model has no UB and the result is the model's. -/
theorem matchone_pspec (C : EquivLean.Demo.XLang.TinyRegex.Ctx) (tok : Tok) (b : Nat) (c : Int)
    (kC : BlockKind) (m : Mem)
    (hC : m.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
      .arr (C.B.toList.map fun (x : Nat) => .int (x : Int))⟩) (hn : 26 ≤ m.next)
    (hB : ∀ x ∈ C.B.toList, x < 256) (hTok : TokOK C.B tok) (hb0 : 0 < b) (hb : b < 256)
    (hcb : c = sc b) :
    pholds (evalCall ctx "matchone" [tokV 24 tok, .int c] m)
      (fun r => (EquivLean.Demo.XLang.TinyRegex.matchone C tok b).2 = 0 ∧
        ∃ v, r.1 = .ret (some (.int v)) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
          (v ≠ 0 ↔ (EquivLean.Demo.XLang.TinyRegex.matchone C tok b).1 = true) ∧
          (∀ b', b' < m.next → r.2.blocks b' = m.blocks b') ∧ m.next ≤ r.2.next) := by
  obtain ⟨hty, hch, hcls⟩ := hTok
  have hc : -128 ≤ c ∧ c ≤ 127 := by rw [hcb]; exact sc_range hb
  intro r hr
  by_cases h89 : tok.type = 8 ∨ tok.type = 9
  · obtain ⟨hk1, e, hke, he, he0⟩ := hcls h89
    have heB : C.B[e] = 0 := by rw [← getElem!_pos C.B e he]; exact he0
    have he' : e < (C.B.toList.map fun (x : Nat) => (x : Int)).length := by rw [xs_length]; exact he
    have he0' : (C.B.toList.map fun (x : Nat) => (x : Int)).getD e 0 = 0 := by
      rw [xs_getD, bget_lt he, heB]; rfl
    have hxs : ∀ x ∈ (C.B.toList.map fun (x : Nat) => (x : Int)), 0 ≤ x ∧ x ≤ 255 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := hB y hy
      omega
    have hblk : m.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
        .arr ((C.B.toList.map fun (x : Nat) => (x : Int)).map .int)⟩ := by
      rw [hC, List.map_map]; rfl
    have hc0 : c ≠ 0 := by rw [hcb]; exact sc_ne_zero hb0 hb
    have htv : tokV 24 tok = .agg [.int tok.type, .agg [.undef, .ptr (.loc 24 [.idx tok.ccl])]] := by
      simp only [tokV, h89, ite_true]
    rw [htv] at hr
    obtain ⟨v, h1, h2, h3, h4, h5, h6⟩ := matchone_cls_pspec _ tok.type tok.ccl e c kC _ m hblk ⟨false, 40, rfl⟩ hn
      hc hc0 hxs h89 hk1 hke he' he0' r hr
    have hbr := matchcharclass_cclC C.B hB b hb0 hb tok.ccl e hk1 hke he heB 0
    rw [← hcb] at hbr
    refine ⟨?_, v, h1, h2, h3, ?_, h5, h6⟩
    · rcases h89 with h | h <;>
        simp only [EquivLean.Demo.XLang.TinyRegex.matchone, EquivLean.Demo.XLang.TinyRegex.DOT,
          EquivLean.Demo.XLang.TinyRegex.CHAR_CLASS, EquivLean.Demo.XLang.TinyRegex.INV_CHAR_CLASS, h, hbr] <;> rfl
    · rw [h4]
      rcases h89 with h | h <;>
        simp only [EquivLean.Demo.XLang.TinyRegex.matchone, EquivLean.Demo.XLang.TinyRegex.DOT,
          EquivLean.Demo.XLang.TinyRegex.CHAR_CLASS, EquivLean.Demo.XLang.TinyRegex.INV_CHAR_CLASS, h, hbr] <;> rfl
  · have h8 : tok.type ≠ 8 := fun h => h89 (Or.inl h)
    have h9 : tok.type ≠ 9 := fun h => h89 (Or.inr h)
    have htv : tokV 24 tok = .agg [.int tok.type, .agg [.int tok.ch, .undef]] := by
      simp only [tokV, h89, ite_false]
    rw [htv] at hr
    obtain ⟨v, m', -, hpost, hK⟩ := holds_returns_elim (holds_of_eq_ok hr)
      (matchone_ch_spec tok.type tok.ch c m hc hty hch h8 h9)
    subst hK
    obtain ⟨⟨w, hw, hw1, hw2, hwi⟩, hfa, hfb⟩ := hpost
    subst hw
    obtain ⟨hmu, hmiff⟩ := matchone_ch_bridge C tok hb h8 h9
    refine ⟨hmu, w, rfl, hw1, hw2, ?_, fun b' hb' => hfb b' (List.not_mem_nil) hb', hfa⟩
    rw [hwi, hmiff, hcb]

end EquivLean.Demo.XLang.TinyRegex.C
