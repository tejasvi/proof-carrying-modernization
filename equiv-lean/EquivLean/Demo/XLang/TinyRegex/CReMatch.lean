import EquivLean.Demo.XLang.TinyRegex.CReMatchp
import EquivLean.Demo.XLang.TinyRegex.CCompile

/-!
# tiny-regex-c → model, C side: `re_match` from program start

`cRun p t` runs `re_match(p, t, &ml)` from program start (`cMem`: the module's initial memory,
then the pattern in block 26 and the text in block 27 as read-only C strings and `ml` in block 28
as an `int` on the caller's stack); `mlOf` reads `ml`.  `re_match_pspec`: for the bytes of two C
strings, every outcome has no model UB, returns the model's `reMatch p t` value and leaves its
`matchlength` in `ml`, in the shape eq-aeneas's `cspec_of_pspec` takes.  Proof: the C runs in the
hypothesis; the two calls use `re_compile_spec` (with `initMem_ccl_buf`, `initMem_re_compiled`)
and `re_matchp_pspec` (with `compile_wf`).
-/

open CIR EquivLean.Cir EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex (Tok)

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- The memory at the call `re_match(p, t, &ml)` from program start: the module's initial memory,
then the pattern (block 26) and the text (block 27) as read-only C strings, and `ml` (block 28) as
an `int` on the caller's stack. -/
def cMem (p t : List Nat) : Mem :=
  ((((module.initMem.alloc .readonly (.array (.int true 8) (p.length + 1))
    (.arr ((patL p).map .int))).2.alloc .readonly (.array (.int true 8) (t.length + 1))
    (.arr ((patL t).map .int))).2.alloc .stack (.int true 32) (.int 0)).2)

/-- `re_match(p, t, &ml)` from program start, for the bytes `p` and `t` of two C strings. -/
def cRun (p t : List Nat) : CIR.Res (Exit × Mem) :=
  evalCall ctx "re_match" [.ptr (.loc 26 [.idx 0]), .ptr (.loc 27 [.idx 0]), .ptr (.loc 28 [])] (cMem p t)

/-- The value of `ml` (block 28) in a memory. -/
def mlOf (m : Mem) : Option Val := (m.blocks 28).map (·.val)

theorem cMem_next (p t : List Nat) : (cMem p t).next = 29 := by
  simp [cMem, Mem.alloc, initMem_next]

theorem cMem_blocks (p t : List Nat) (b : Nat) :
    (cMem p t).blocks b =
      upd (upd (upd module.initMem.blocks 26
        (some ⟨.readonly, true, .array (.int true 8) (p.length + 1), .arr ((patL p).map .int)⟩)) 27
        (some ⟨.readonly, true, .array (.int true 8) (t.length + 1), .arr ((patL t).map .int)⟩)) 28
        (some ⟨.stack, true, .int true 32, .int 0⟩) b := by
  simp [cMem, Mem.alloc, initMem_next]

theorem reMatch_eq (p t : List Nat) :
    EquivLean.Demo.XLang.TinyRegex.reMatch p t =
      EquivLean.Demo.XLang.TinyRegex.reMatchp (EquivLean.Demo.XLang.TinyRegex.compile p.toArray).1 t.toArray 0 := by
  have h := EquivLean.Demo.XLang.TinyRegex.compile_ub_eq_zero p.toArray
  unfold EquivLean.Demo.XLang.TinyRegex.reMatch
  generalize EquivLean.Demo.XLang.TinyRegex.compile p.toArray = c at h ⊢
  obtain ⟨cp, ub⟩ := c
  simp only at h ⊢
  subst h; rfl

theorem frame_ne {m m' : Mem} (h : Frame m m' [25, 24]) :
    ∀ b, b ≠ 25 → b ≠ 24 → b < m.next → m'.blocks b = m.blocks b :=
  fun b h1 h2 h3 => h.2 b (by simp [h1, h2]) h3

/-- **`re_match` from program start**: for the bytes `p` and `t` of two C strings, every outcome of
`re_match(p, t, &ml)` has no model UB, returns the model's value and leaves the model's
`matchlength` in `ml` (the shape `cspec_of_pspec` takes). -/
theorem re_match_pspec (p t : List Nat) (hp : ∀ b ∈ p, 0 < b ∧ b < 256) (ht : ∀ b ∈ t, 0 < b ∧ b < 256)
    (a : Exit × Mem) (ha : cRun p t = .ok a) :
    (EquivLean.Demo.XLang.TinyRegex.reMatch p t).2.2 = 0 ∧
      a.1 = .ret (some (.int (EquivLean.Demo.XLang.TinyRegex.reMatch p t).1)) ∧
      mlOf a.2 = some (.int (EquivLean.Demo.XLang.TinyRegex.reMatch p t).2.1) := by
  have hs : (evalCall ctx "re_match" [.ptr (.loc 26 [.idx 0]), .ptr (.loc 27 [.idx 0]),
      .ptr (.loc 28 [])] (cMem p t)).holds (· = a) := by unfold cRun at ha; rw [ha]; rfl
  have cirH_cn : (cMem p t).next = 29 := cMem_next p t
  cir_hstep hs
  cir_hrun_c hs
  -- `re_compile(pattern)`
  obtain ⟨v1, m1, -, hp1, hs⟩ := holds_returns_elim hs (re_compile_spec p 26 .readonly
    (.array (.int true 8) (p.length + 1)) _ hp
    (by simp (disch := omega) only [upd_apply_ne, cMem_blocks, upd_apply_same]) ⟨true, p.length + 1, rfl⟩
    (by simp (disch := omega) only [upd_apply_ne, cMem_blocks, initMem_re_compiled])
    (by simp (disch := omega) only [upd_apply_ne, cMem_blocks, initMem_ccl_buf])
    (by dsimp only; omega) (by dsimp only; omega) (by decide))
  obtain ⟨hcpost, hframe⟩ := hp1
  have cirH_fr1 := frame_ne hframe
  have cirH_nx1 := hframe.1
  dsimp only at cirH_fr1 cirH_nx1
  have hv1 : v1 = some (cpPtr (EquivLean.Demo.XLang.TinyRegex.compile p.toArray).1) := by
    unfold CompPost at hcpost
    rcases hc : (EquivLean.Demo.XLang.TinyRegex.compile p.toArray).1 with _ | ⟨P, B⟩ <;> rw [hc] at hcpost
    · exact hcpost
    · exact hcpost.1
  subst hv1
  cir_hrun_c hs
  -- `re_matchp(re_compile(pattern), text, matchlength)`
  have hcp : ∀ P B, (EquivLean.Demo.XLang.TinyRegex.compile p.toArray).1 = some (P, B) → ∃ kR kC,
      m1.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (P.toList.map (tokV 24))⟩ ∧
      m1.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
        .arr (B.toList.map fun (x : Nat) => .int (x : Int))⟩ ∧
      P.size = 30 ∧ (∀ x ∈ B.toList, x < 256) ∧ (∀ (i : Nat) (hi : i < P.size), TokOK B P[i]) := by
    intro P B hc
    unfold CompPost at hcpost
    rw [hc] at hcpost
    obtain ⟨hPs, hBs, hB, htok⟩ := EquivLean.Demo.XLang.TinyRegex.compile_wf p hp P B hc
    refine ⟨.global, .global, hcpost.2.1, hcpost.2.2, hPs, hB, fun i hi => ?_⟩
    have hget : P[i]! = P[i] := getElem!_pos P i hi
    obtain ⟨h1, h2, h3⟩ := htok i (by omega)
    rw [hget] at h1 h2 h3
    exact ⟨h1, h2, fun hcl => by rw [hBs]; exact h3 hcl⟩
  obtain ⟨⟨e2, m2⟩, -, hp2, hs⟩ := holds_pspec_elim hs (re_matchp_pspec
    (EquivLean.Demo.XLang.TinyRegex.compile p.toArray).1 t 27 28 m1 .readonly .stack
    (.array (.int true 8) (t.length + 1)) (.int 0) hcp
    (by simp (disch := omega) only [cirH_fr1, upd_apply_ne, cMem_blocks, upd_apply_same]) ⟨true, t.length + 1, rfl⟩
    (by simp (disch := omega) only [cirH_fr1, upd_apply_ne, cMem_blocks, upd_apply_same])
    (by decide) (by omega) (by omega) (by omega) (by decide) (by decide) (by decide) ht)
  obtain ⟨hub2, he2, hbl2, hfr2, hnx2⟩ := hp2
  dsimp only at hub2 he2 hbl2 hfr2 hnx2
  subst he2
  cir_hrun_c hs
  subst hs
  rw [reMatch_eq]
  refine ⟨hub2, rfl, ?_⟩
  simp (disch := omega) only [mlOf, Mem.endScope, killRange_of_lt, upd_apply_ne, hbl2, Option.map_some]

/-- `re_match_pspec` is the hypothesis of `cspec_of_pspec` (trx-rs `Equiv.lean`) for `cRun`,
`mlOf`. -/
example : ∀ (p t : List Nat), (∀ b ∈ p, 0 < b ∧ b < 256) → (∀ b ∈ t, 0 < b ∧ b < 256) →
    ∀ a, cRun p t = .ok a →
      (EquivLean.Demo.XLang.TinyRegex.reMatch p t).2.2 = 0 ∧
        a.1 = .ret (some (.int (EquivLean.Demo.XLang.TinyRegex.reMatch p t).1)) ∧
        mlOf a.2 = some (.int (EquivLean.Demo.XLang.TinyRegex.reMatch p t).2.1) :=
  re_match_pspec

end EquivLean.Demo.XLang.TinyRegex.C
