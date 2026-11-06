-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg44X.lean (sha256 c27f6029dfb78d2a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg44X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunSeg44X`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem run_tseg44 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J44 g g.args σ0 fr σ)
    (c45 : cuts.lookup 45 = none) (c46 : cuts.lookup 46 = none) (c47 : cuts.lookup 47 = none)
    (c48 : cuts.lookup 48 = some (fun fr' σ' => runVs 48 g.args σ0 fr' σ' < runVs 44 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 44 fr σ := by
  obtain ⟨-, -, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, wA, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, f13, hH, hKX, hXA, hg, hinits, hstat,
    hinit⟩ := h
  have hiC : σ.initOf "Cbtrn02c$TranCatBalRecord" = .done := by rw [initOf_of_inits' hinits]; exact i6
  have hlt : wA < σ.next := by
    obtain ⟨-, -, fsA, hAh, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hAh
  have hg' := Hide.intro hg
  clear hg
  unfold RunThinWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorTCSig, ctorTCSpec,
    fields_get_cons, fields_get_nil, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
