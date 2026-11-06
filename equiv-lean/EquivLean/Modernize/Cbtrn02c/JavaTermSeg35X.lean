-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg35X.lean (sha256 24bd05bf7923d283...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg35X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunSeg35X`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem run_tseg35 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J35 g g.args σ0 fr σ)
    (c36 : cuts.lookup 36 = none) (c37 : cuts.lookup 37 = none) (c38 : cuts.lookup 38 = none)
    (c39 : cuts.lookup 39 = none) (c40 : cuts.lookup 40 = none) (c41 : cuts.lookup 41 = none)
    (c42 : cuts.lookup 42 = none) (c43 : cuts.lookup 43 = none)
    (c44 : cuts.lookup 44 = some (fun fr' σ' => runVs 44 g.args σ0 fr' σ' < runVs 35 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 35 fr σ := by
  obtain ⟨-, -, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, hH, hKX, hg, hinits, hstat, hinit⟩ := h
  have hiA : σ.initOf "Cbtrn02c$AccountRecord" = .done := by rw [initOf_of_inits35 hinits]; exact i3
  have hlt : wX < σ.next := by
    obtain ⟨-, fsX, hXh, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hXh
  have hg' := Hide.intro hg
  clear hg
  unfold RunThinWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorACSig, ctorACSpec,
    fields_get_cons, fields_get_nil, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
