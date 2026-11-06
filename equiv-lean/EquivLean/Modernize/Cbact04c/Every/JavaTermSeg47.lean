-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg47.lean (sha256 e80fd2e08eb37a55...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg47
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg47`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg47 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (h : JI42 g g.args σ0 fr σ)
    (c48 : cuts.lookup 48 = none) (c49 : cuts.lookup 49 = none) (c50 : cuts.lookup 50 = none)
    (c51 : cuts.lookup 51 = none) (c52 : cuts.lookup 52 = none) (c53 : cuts.lookup 53 = none)
    (c54 : cuts.lookup 54 = none) (c55 : cuts.lookup 55 = none) (c56 : cuts.lookup 56 = none)
    (c57 : cuts.lookup 57 = some (fun fr' σ' => runVs B 57 g.args σ0 fr' σ' < runVs B 47 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 47 fr σ := by
  obtain ⟨res, ld, lw, lr, A, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht, hres, hdisp,
    hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, v17, f17⟩ := h
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hg
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, ctorACSig, ctorACF, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
