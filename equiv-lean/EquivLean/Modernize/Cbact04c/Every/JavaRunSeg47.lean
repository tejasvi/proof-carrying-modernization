import EquivLean.Modernize.Cbact04c.Every.JavaRunResInit
import EquivLean.Modernize.Cbact04c.Every.JavaRunSpecEqs

/-!
# CBACT04C → Java, `run`: statements 47–56 (the account object)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg47 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (h : JI42 g g.args σ0 fr σ)
    (c48 : cuts.lookup 48 = none) (c49 : cuts.lookup 49 = none) (c50 : cuts.lookup 50 = none)
    (c51 : cuts.lookup 51 = none) (c52 : cuts.lookup 52 = none) (c53 : cuts.lookup 53 = none)
    (c54 : cuts.lookup 54 = none) (c55 : cuts.lookup 55 = none) (c56 : cuts.lookup 56 = none)
    (c57 : cuts.lookup 57 = some (JI57 g g.args σ0)) :
    RunWPc g σ0 cuts 47 fr σ := by
  obtain ⟨res, ld, lw, lr, A, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht, hres, hdisp,
    hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, v17, f17⟩ := h
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hg
  unfold RunWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, ctorACSig, ctorACF]
  spec_eqs!
  refine ⟨res, ld, lw, lr, A, .ref σ.next, initAt_of ht hres hdisp hw hr hr0 hd0 hw0 hl0 hA0 hd1
    hd2 hd3 (Hide.elim hg') (Hide.elim hin') ⟨by jomega, fun x hx _ => ?_⟩ (by assumption) ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩
  · chain_simp
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41]; done)
    | exact ⟨_, by first | (frame_simp [f17]; done) | (frame_simp [f17]; rfl)⟩

end EquivLean.Modernize.Cbact04c.Java
