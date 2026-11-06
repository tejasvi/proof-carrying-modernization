-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg42.lean (sha256 7954113faea8e54a...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg42
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg42`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg42 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (h : JI42 g g.args σ0 fr σ)
    (c43 : cuts.lookup 43 = none) (c44 : cuts.lookup 44 = none) (c45 : cuts.lookup 45 = none)
    (c46 : cuts.lookup 46 = none) (c47 : cuts.lookup 47 = some (fun fr' σ' => runVs B 47 g.args σ0 fr' σ' < runVs B 42 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 42 fr σ := by
  obtain ⟨res, ld, lw, lr, A, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht, hres, hdisp,
    hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, v17, f17⟩ := h
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hg
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, ctorDCSig, ctorDCF, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
