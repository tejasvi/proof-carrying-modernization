-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg57.lean (sha256 afac65d524a1baa6...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg57
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg57`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg57 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (h : JI57 g g.args σ0 fr σ)
    (c58 : cuts.lookup 58 = none) (c59 : cuts.lookup 59 = none) (c60 : cuts.lookup 60 = none)
    (c61 : cuts.lookup 61 = none) (c62 : cuts.lookup 62 = none)
    (c63 : cuts.lookup 63 = some (fun fr' σ' => runVs B 63 g.args σ0 fr' σ' < runVs B 57 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 57 fr σ := by
  obtain ⟨res, ld, lw, lr, A, acctV, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht, hres,
    hdisp, hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, f16, v17, f17⟩ := h
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hg
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
