-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermRunL75.lean (sha256 12ebb950396d32b4...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL75
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunRunL75`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_tseg75 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : L75X g g.args σ0 fr σ)
    (hc : ∀ k, 76 ≤ k → k ≤ 82 → cuts.lookup k = none)
    (c65 : cuts.lookup 65 = some (fun fr' σ' => runVs 65 g.args σ0 fr' σ' < runVs 75 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 75 fr σ := by
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
  unfold RunThinWPcX
  jvc [runCX, writeRejectSig, writeRejectSpec, postTransactionSig, postTransactionSpec, Grows,
    narrow_long, narrow_cls, G.args, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
