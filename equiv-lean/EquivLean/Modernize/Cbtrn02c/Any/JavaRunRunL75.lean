import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunH3

/-!
# CBTRN02C → Java: `run`'s main loop after `validateTran` (statement 75)

A rejected transaction: the reject counter, `writeReject`, back to 65.  A valid one:
`postTransaction`; a new id: back to 65; a written id: `run` returns (abended).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_seg75 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : L75X g g.args σ0 fr σ)
    (hc : ∀ k, 76 ≤ k → k ≤ 82 → cuts.lookup k = none)
    (c65 : cuts.lookup 65 = some (L65X g g.args σ0)) :
    RunWPcX g σ0 cuts 75 fr σ := by
  obtain ⟨A, k, next, c, tx, rej, et, xsD, d, hL, f14, f9, f10, f30, f15, f4, ha1, hlenD, hxk, hk, hnext,
    htx, hrej, hc', hstx, hkeep, hg, hin, hst⟩ := h
  have hI : Inits σ := by
    obtain ⟨-, -, hI0⟩ := hpre
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI0
    have e := fun c => initOf_of_inits hin c
    exact ⟨by rw [e]; exact i1, by rw [e]; exact i2, by rw [e]; exact i3, by rw [e]; exact i4,
      by rw [e]; exact i5, by rw [e]; exact i6, by rw [e]; exact i7, by rw [e]; exact i8⟩
  have hkeepP := Hide.intro hpre
  have hkeepG := Hide.intro hg
  have hkeepI := Hide.intro hI
  clear hpre hg
  obtain ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩ := hL
  have c76 := hc 76 (by omega) (by omega)
  have c77 := hc 77 (by omega) (by omega)
  have c78 := hc 78 (by omega) (by omega)
  have c79 := hc 79 (by omega) (by omega)
  have c80 := hc 80 (by omega) (by omega)
  have c81 := hc 81 (by omega) (by omega)
  have c82 := hc 82 (by omega) (by omega)
  clear hc
  unfold RunWPcX
  jvc [runCX, writeRejectSig, writeRejectSpec, postTransactionSig, postTransactionSpec, Grows,
    narrow_long, narrow_cls, G.args]
  case isTrue.left =>
    obtain ⟨x, a, -, -, -, -, -, -, -, hPF⟩ := seg75_valid (Hide.elim hkeepP) (Hide.elim hkeepG)
      (Hide.elim hkeepI) (Hide.elim hkeep) ha1 hxk hk hcond
    exact ⟨⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩, rfl, hPF⟩
  case isTrue.right.normal.some.int.isTrue =>
    rename_i hpost
    obtain ⟨-, hMV, -, hFr, -⟩ := Hide.elim hkeep
    obtain ⟨x, a, hv0, hfx, hfa, htv, hxv, hav, ha10, hPF⟩ := seg75_valid (Hide.elim hkeepP)
      (Hide.elim hkeepG) (Hide.elim hkeepI) (Hide.elim hkeep) ha1 hxk hk hcond
    have hP := hpost ⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩ rfl hPF
    by_cases hdu : ∃ x0 ∈ (g.st k).tranW, Model.tId x0 = Model.tId (g.trec k)
    · obtain ⟨x0, hx0, he0⟩ := hdu
      exact (hP.2.1 x0 hx0 he0).1.elim
    · obtain ⟨hW1, hfr1, hAd1⟩ := hP.1 (fun x0 hx0 he0 => hdu ⟨x0, hx0, he0⟩)
      have hnd : Model.tId (g.trec k) ∉ (g.st k).tranW.map Model.tId := by
        intro hm
        obtain ⟨x0, hx0, he0⟩ := List.mem_map.1 hm
        exact hdu ⟨x0, hx0, he0⟩
      exact l65x_post ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩ f14 f4 f9 f10 ha1 hlenD
        hnext hk ha10 hstx hv0 hfx hfa hnd hMV htv hxv hav hFr (Hide.elim hkeepG) hW1 hfr1 hAd1
        hP.2.2.1 hP.2.2.2
  case isTrue.right.normal.some.int.isFalse =>
    rename_i hpost
    obtain ⟨x, a, hv0, hfx, hfa, -, -, -, -, hPF⟩ := seg75_valid (Hide.elim hkeepP)
      (Hide.elim hkeepG) (Hide.elim hkeepI) (Hide.elim hkeep) ha1 hxk hk ‹_›
    have hP := hpost ⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩ rfl hPF
    by_cases hdu : ∃ x0 ∈ (g.st k).tranW, Model.tId x0 = Model.tId (g.trec k)
    · obtain ⟨x0, hx0, he0⟩ := hdu
      exact out_post_dup hk hstx hv0 hfx hfa (List.mem_map.2 ⟨x0, hx0, he0⟩) (hP.2.1 x0 hx0 he0).2
    · exact absurd (Value.int.inj (hP.1 (fun x0 hx0 he0 => hdu ⟨x0, hx0, he0⟩)).1) hcond
  case isFalse.left =>
    obtain ⟨-, hRin, -⟩ := Hide.elim hkeepP
    obtain ⟨hd, htv⟩ := trec_at hRin (Hide.elim hkeepG) ha1 hxk hk
    exact wrPre_of (Hide.elim hkeep).1 hd htv (vreason_ne_cases (vreason_ne_of hcond))
  case isFalse.right.normal =>
    obtain ⟨hW, hMV, hAd, hFr, -⟩ := Hide.elim hkeep
    exact l65x_reject (Hide.elim hkeepP) ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩ f14
      f4 f9 ha1 hlenD hxk hnext hk hstx (vreason_ne_of hcond) hW hMV hAd hFr (Hide.elim hkeepG)
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  all_goals
    rename_i hpost
    obtain ⟨x, a, -, -, -, -, -, -, -, hPF⟩ := seg75_valid (Hide.elim hkeepP) (Hide.elim hkeepG)
      (Hide.elim hkeepI) (Hide.elim hkeep) ha1 hxk hk hcond
    have hP := hpost ⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩ rfl hPF
    by_cases hdu : ∃ x0 ∈ (g.st k).tranW, Model.tId x0 = Model.tId (g.trec k)
    · obtain ⟨x0, hx0, he0⟩ := hdu
      exact (hP.2.1 x0 hx0 he0).1.elim
    · exact (hP.1 (fun x0 hx0 he0 => hdu ⟨x0, hx0, he0⟩)).1.elim

end EquivLean.Modernize.Cbtrn02c.Java
