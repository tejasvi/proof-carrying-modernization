-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg48X.lean (sha256 018072179137244d...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg48X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunSeg48X`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem run_tseg48 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J48 g g.args σ0 fr σ)
    (c49 : cuts.lookup 49 = none) (c50 : cuts.lookup 50 = none) (c51 : cuts.lookup 51 = none)
    (c52 : cuts.lookup 52 = none) (c53 : cuts.lookup 53 = none) (c54 : cuts.lookup 54 = none)
    (c55 : cuts.lookup 55 = none) (c56 : cuts.lookup 56 = none) (c57 : cuts.lookup 57 = none)
    (c58 : cuts.lookup 58 = none) (c59 : cuts.lookup 59 = none) (c60 : cuts.lookup 60 = none)
    (c61 : cuts.lookup 61 = none) (c62 : cuts.lookup 62 = none) (c63 : cuts.lookup 63 = none)
    (c64 : cuts.lookup 64 = none) (c65 : cuts.lookup 65 = some (fun fr' σ' => runVs 65 g.args σ0 fr' σ' < runVs 48 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 48 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, wA, wC, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, f13, f29, hH, hKX, hXA, hAC, hg,
    hinits, hstat, hinit⟩ := h
  have hiT : σ.initOf "Cbtrn02c$TranRecord" = .done := by rw [initOf_of_inits'' hinits]; exact i8
  have hlt : wC < σ.next := by
    obtain ⟨-, -, -, ⟨fsC, hCh, -⟩, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hCh
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  clear hg hin
  unfold RunThinWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorTRSig, ctorTRSpec,
    fields_get_cons, fields_get_nil, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
