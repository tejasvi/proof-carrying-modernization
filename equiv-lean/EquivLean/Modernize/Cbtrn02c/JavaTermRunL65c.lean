-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermRunL65c.lean (sha256 bf0eb8f3a2523b0a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL65c
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twin of `run_seg65` (`JavaRunRunL65c`)

The statement and the preamble of the original over the thin cut list (each cut assertion a variant
comparison), its two cases (the end-of-file flag clear; set), each with the original's `jvc` call;
calls by `callWPThin`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_tseg65 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : L65X g g.args σ0 fr σ)
    (hc : ∀ k, 66 ≤ k → k ≤ 74 → cuts.lookup k = none)
    (c83 : cuts.lookup 83 = some (fun fr' σ' => runVs 83 g.args σ0 fr' σ' < runVs 65 g.args σ0 fr σ))
    (c75 : cuts.lookup 75 = some (fun fr' σ' => runVs 75 g.args σ0 fr' σ' < runVs 65 g.args σ0 fr σ))
    (c65 : cuts.lookup 65 = some (fun fr' σ' => runVs 65 g.args σ0 fr' σ' < runVs 65 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 65 fr σ := by
  obtain ⟨A, k, next, z, tx, rej, et, xsD, hL, f14, f4, f9, f10, ha1, hlenD, hnext, hk, hz, htx, hrej,
    hstx, hkeep, hg, hin, hst⟩ := h
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
  have c66 := hc 66 (by omega) (by omega)
  have c67 := hc 67 (by omega) (by omega)
  have c68 := hc 68 (by omega) (by omega)
  have c69 := hc 69 (by omega) (by omega)
  have c70 := hc 70 (by omega) (by omega)
  have c71 := hc 71 (by omega) (by omega)
  have c72 := hc 72 (by omega) (by omega)
  have c73 := hc 73 (by omega) (by omega)
  have c74 := hc 74 (by omega) (by omega)
  clear hc
  rcases hz with rfl | ⟨rfl, hkn⟩
  · unfold RunThinWPcX
    jvc [runCX, validateTranSig, validateTranSpec, Grows, narrow_long, narrow_cls, G.args, runVs]
  · unfold RunThinWPcX
    jvc [runCX, validateTranSig, validateTranSpec, Grows, narrow_long, narrow_cls, G.args, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
