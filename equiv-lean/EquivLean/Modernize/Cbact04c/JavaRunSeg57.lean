import EquivLean.Modernize.Cbact04c.JavaRunResInit
import EquivLean.Modernize.Cbact04c.JavaRunSpecEqs

/-!
# CBACT04C → Java, `run`: statements 57–62 (the transaction object, its first strings)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg57 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (h : JI57 g g.args σ0 fr σ)
    (c58 : cuts.lookup 58 = none) (c59 : cuts.lookup 59 = none) (c60 : cuts.lookup 60 = none)
    (c61 : cuts.lookup 61 = none) (c62 : cuts.lookup 62 = none)
    (c63 : cuts.lookup 63 = some (JI63 g g.args σ0)) :
    RunWPc g σ0 cuts 57 fr σ := by
  obtain ⟨res, ld, lw, lr, A, acctV, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht, hres,
    hdisp, hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, f16, v17, f17⟩ := h
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hg
  unfold RunWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec]
  refine ⟨res, ld, lw, lr, A, acctV, σ.next, ?_, initAt_of ht hres hdisp hw hr hr0 hd0 hw0 hl0 hA0
    hd1 hd2 hd3 (Hide.elim hg') (Hide.elim hin') ⟨by jomega, fun x hx _ => ?_⟩ (by assumption) ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, (Hide.elim hg').1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · chain_simp
  · frame_simp [f1]
  · frame_simp [f36]
  · frame_simp [f40]
  · frame_simp [f8]
  · frame_simp [f37]
  · frame_simp [f24]
  · frame_simp [f10]
  · frame_simp [f19]
  · frame_simp [f20]
  · frame_simp [f21]
  · frame_simp [f41]
  · frame_simp [f16]
  · frame_simp []
  · refine ⟨_, by chain_simp, fun k hk => ?_⟩
    simp only [keysTR, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fields_get_cons]
  · first | (frame_simp []; done) | (frame_simp []; rfl)
  · chain_simp
  · exact ⟨_, by first | (frame_simp []; done) | (frame_simp []; rfl)⟩
  · exact ⟨_, by first | (frame_simp []; done) | (frame_simp []; rfl)⟩
  · exact ⟨_, by first | (frame_simp []; done) | (frame_simp []; rfl)⟩
  · exact ⟨_, by first | (frame_simp []; done) | (frame_simp []; rfl)⟩
  · exact ⟨_, by first | (frame_simp [f17]; done) | (frame_simp [f17]; rfl)⟩

end EquivLean.Modernize.Cbact04c.Java
