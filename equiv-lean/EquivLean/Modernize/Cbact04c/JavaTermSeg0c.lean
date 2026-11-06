-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg0c.lean (sha256 acaf559e4e02c1f5...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg0c
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg0c`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg0 (g : G) (σ0 : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = some (fun _ _ => True)) :
    RunThinWPc g σ0 cuts 0 (Frame.init true g.args) σ0 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre.2.2
  clear hpre
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, fields_get_cons, fields_get_nil, G.args, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
