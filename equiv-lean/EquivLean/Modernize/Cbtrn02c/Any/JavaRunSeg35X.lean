import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem initOf_of_inits35 {σ σ0 : State} (h : σ.inits = σ0.inits) (c : ClassName) :
    σ.initOf c = σ0.initOf c := by
  simp only [State.initOf, h]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Statements 35–43: `acctWs` built (seven strings of spaces, the constructor). -/
theorem run_seg35 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J35 g g.args σ0 fr σ)
    (c36 : cuts.lookup 36 = none) (c37 : cuts.lookup 37 = none) (c38 : cuts.lookup 38 = none)
    (c39 : cuts.lookup 39 = none) (c40 : cuts.lookup 40 = none) (c41 : cuts.lookup 41 = none)
    (c42 : cuts.lookup 42 = none) (c43 : cuts.lookup 43 = none)
    (c44 : cuts.lookup 44 = some (J44 g g.args σ0)) :
    RunWPcX g σ0 cuts 35 fr σ := by
  obtain ⟨-, -, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, hH, hKX, hg, hinits, hstat, hinit⟩ := h
  have hiA : σ.initOf "Cbtrn02c$AccountRecord" = .done := by rw [initOf_of_inits35 hinits]; exact i3
  have hlt : wX < σ.next := by
    obtain ⟨-, fsX, hXh, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hXh
  have hg' := Hide.intro hg
  clear hg
  unfold RunWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorACSig, ctorACSpec,
    fields_get_cons, fields_get_nil]
  rename_i vR σA hA
  obtain ⟨hA1, hA2, hA3, hA4, hA5, -⟩ := hA σ.next _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by chain_simp)
  have hgA : Grows σ σA := by grows_tac
  obtain ⟨hP, hX⟩ := Hide.elim hH
  refine ⟨lC, lK, wX, σ.next, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    Hide.intro ⟨hP.grows hgA, hX.grows hgA, wsobj_of_setFields hA1 (by decide) (by simp)⟩,
    hKX, hlt, grows_trans (Hide.elim hg') hgA, hA4, hA5, ?_⟩
  any_goals (frame_simp [f32, f0, f16, f31, f8, f11, f12, f6]; done)
  rw [initOf_of_inits35 hA4]

end EquivLean.Modernize.Cbtrn02c.Java
