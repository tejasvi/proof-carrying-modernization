-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg0X.lean (sha256 2fbf196bc6ddf18e...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg0X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunSeg0X`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem run_tseg0 (g : G) (σ0 : State) (cuts : Cuts) (hpre : RunPreGX g g.args σ0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c11 : cuts.lookup 11 = none)
    (c12 : cuts.lookup 12 = some (fun _ _ => True)) :
    RunThinWPcX g σ0 cuts 0 (Frame.init true g.args) σ0 := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, ⟨et3, xs3, h3, hl3, hf3⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hlen3 := forall2_length hf3
  clear hf3
  unfold RunThinWPcX
  jvc [runCX, inlineFuel, G.args, Grows, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
