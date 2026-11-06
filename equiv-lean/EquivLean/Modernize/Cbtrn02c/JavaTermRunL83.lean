-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermRunL83.lean (sha256 423941b4a13f1e66...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL83
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunRunL83`

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
theorem run_tseg83 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : J83X g g.args σ0 fr σ)
    (hc : ∀ k, 84 ≤ k → k ≤ 97 → cuts.lookup k = none) :
    RunThinWPcX g σ0 cuts 83 fr σ := by
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
  unfold RunThinWPcX
  jvc [runCX, padNumSig, padNumSpec, Grows, narrow_long, narrow_cls, G.args, evalDynamic,
    concatRecipe, Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr,
    Native.primStr, JType.isRef, jstrLitT, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
