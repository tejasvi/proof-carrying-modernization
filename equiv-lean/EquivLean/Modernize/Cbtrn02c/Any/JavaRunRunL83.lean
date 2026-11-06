import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunOutX

/-!
# CBTRN02C → Java: `run`'s exit (statements 83 to 97)

The counts of processed and rejected transactions, the return code 4 if a transaction was
rejected, the end line, and the return of the `Result`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_seg83 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : J83X g g.args σ0 fr σ)
    (hc : ∀ k, 84 ≤ k → k ≤ 97 → cuts.lookup k = none) :
    RunWPcX g σ0 cuts 83 fr σ := by
  obtain ⟨A, tx, rej, hL, f9, f10, hkeep, hg, hin, hst⟩ := h
  have hI : Inits σ := by
    obtain ⟨-, -, hI0⟩ := hpre
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI0
    have e := fun c => initOf_of_inits hin c
    exact ⟨by rw [e]; exact i1, by rw [e]; exact i2, by rw [e]; exact i3, by rw [e]; exact i4,
      by rw [e]; exact i5, by rw [e]; exact i6, by rw [e]; exact i7, by rw [e]; exact i8⟩
  obtain ⟨fsR, hRh, hRd, -, -, -, -, -, hrc0, -⟩ := (Hide.elim hkeep).2.2.2.1.1
  have hkeepR := Hide.intro hrc0
  clear hrc0
  obtain ⟨xsL, mL, hlD, -⟩ := (Hide.elim hkeep).2.2.2.1.2.1
  have hkeepP := Hide.intro hpre
  have hkeepG := Hide.intro hg
  have hkeepI := Hide.intro hI
  clear hpre hg
  obtain ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩ := hL
  have c84 := hc 84 (by omega) (by omega)
  have c85 := hc 85 (by omega) (by omega)
  have c86 := hc 86 (by omega) (by omega)
  have c87 := hc 87 (by omega) (by omega)
  have c88 := hc 88 (by omega) (by omega)
  have c89 := hc 89 (by omega) (by omega)
  have c90 := hc 90 (by omega) (by omega)
  have c91 := hc 91 (by omega) (by omega)
  have c92 := hc 92 (by omega) (by omega)
  have c93 := hc 93 (by omega) (by omega)
  have c94 := hc 94 (by omega) (by omega)
  have c95 := hc 95 (by omega) (by omega)
  have c96 := hc 96 (by omega) (by omega)
  have c97 := hc 97 (by omega) (by omega)
  clear hc
  unfold RunWPcX
  jvc [runCX, padNumSig, padNumSpec, Grows, narrow_long, narrow_cls, G.args, evalDynamic,
    concatRecipe, Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr,
    Native.primStr, JType.isRef, jstrLitT]
  case left =>
    obtain ⟨htx, -⟩ := Hide.elim hkeep
    obtain ⟨-, hb⟩ := exit_facts (Hide.elim hkeepP)
    refine ⟨tx, 9#32, ⟨rfl, rfl⟩, ?_, by decide, by decide⟩
    rw [htx, toInt_ofNat64 (by jomega)]
    jomega
  case right.normal.isFalse.left =>
    obtain ⟨-, hrj, -⟩ := Hide.elim hkeep
    obtain ⟨hrl, hb⟩ := exit_facts (Hide.elim hkeepP)
    refine ⟨rej, 9#32, ⟨rfl, rfl⟩, ?_, by decide, by decide⟩
    rw [hrj, toInt_ofNat64 (by jomega)]
    jomega
  case right.normal.isFalse.right.normal.isTrue.isFalse.isFalse =>
    obtain ⟨-, hrj, -⟩ := Hide.elim hkeep
    obtain ⟨hrl, hb⟩ := exit_facts (Hide.elim hkeepP)
    have hneg := ‹BitVec.toInt rej < 0›
    rw [hrj, toInt_ofNat64 (by jomega)] at hneg
    exfalso
    jomega
  case right.normal.isFalse.right.normal.isFalse.isFalse.isFalse.isFalse.none =>
    rw [Hide.elim hkeepR] at hd
    cases hd
  case right.normal.isFalse.right.normal.isFalse.isTrue.isFalse.isFalse =>
    obtain ⟨htx, hrj, hstx, hW, -, -⟩ := Hide.elim hkeep
    obtain ⟨hrl, hb⟩ := exit_facts (Hide.elim hkeepP)
    have e1 : (BitVec.toInt tx).natAbs = g.trans.length := by
      rw [htx, toInt_ofNat64 (by jomega), Int.natAbs_natCast, Nat.mod_eq_of_lt (by jomega)]
    have h0 : (BitVec.ofNat 64 ((g.st g.trans.length).rejects % 1000000000)).toInt = 0 := by
      rw [← hrj]
      try rfl
    rw [toInt_ofNat64 (by jomega)] at h0
    have hr0 : (g.st g.trans.length).rejects = 0 := by jomega
    have hrc0 := Hide.elim hkeepR
    clear htx hrj h0
    unfold runPostX
    apply post_exit hW hstx hlD
    case hD' => chain_simp
    case h1 => chain_simp
    case h2 => chain_simp
    case h3 => chain_simp
    case hr => chain_simp
    case hfs =>
      intro f _
      rw [fieldsOf_of hRh]
    case hrc =>
      rw [hrc0, hr0]
      try rfl
    case hf =>
      refine ⟨by simp only [State.next_alloc, State.next_setObj] at *; jomega, fun z hz hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨hz1, hz2⟩ := hm
      chain_simp
  case right.normal.isFalse.right.normal.isFalse.isFalse.isFalse.isFalse.some.isFalse =>
    obtain ⟨htx, hrj, hstx, hW, -, -⟩ := Hide.elim hkeep
    obtain ⟨hrl, hb⟩ := exit_facts (Hide.elim hkeepP)
    have e1 : (BitVec.toInt tx).natAbs = g.trans.length := by
      rw [htx, toInt_ofNat64 (by jomega), Int.natAbs_natCast, Nat.mod_eq_of_lt (by jomega)]
    have e2 : (BitVec.toInt rej).natAbs = (g.st g.trans.length).rejects := by
      rw [hrj, toInt_ofNat64 (by jomega), Int.natAbs_natCast, Nat.mod_eq_of_lt (by jomega)]
    have hpos : 0 < (g.st g.trans.length).rejects := by
      rcases Nat.eq_zero_or_pos (g.st g.trans.length).rejects with h0 | h0
      · exfalso
        apply ‹¬rej = 0#64›
        rw [hrj, h0]
      · exact h0
    clear htx hrj
    unfold runPostX
    apply post_exit hW hstx hlD
    case hD' => chain_simp
    case h1 => chain_simp
    case h2 => chain_simp
    case h3 => chain_simp
    case hr => chain_simp
    case hfs =>
      intro f hf
      rw [fieldsOf_of hRh, Fields.get_set, if_neg (fun h => hf (Prod.mk.inj h).2)]
    case hrc =>
      rw [Fields.get_set, if_pos rfl, if_pos hpos]
      try rfl
    case hf =>
      refine ⟨by simp only [State.next_alloc, State.next_setObj] at *; jomega, fun z hz hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      obtain ⟨hz1, hz2⟩ := hm
      chain_simp

end EquivLean.Modernize.Cbtrn02c.Java
