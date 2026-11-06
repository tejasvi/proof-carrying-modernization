import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem initOf_of_inits' {σ σ0 : State} (h : σ.inits = σ0.inits) (c : ClassName) :
    σ.initOf c = σ0.initOf c := by
  simp only [State.initOf, h]

theorem ne_of_heap_str_plain {σ : State} {a b : Addr} {t : JStr} {c : ClassName}
    {fs : List (FieldKey × Value)} (ha : σ.heap a = some (.str t)) (hb : σ.heap b = some (.plain c fs)) :
    a ≠ b := by
  rintro rfl; rw [ha] at hb; cases hb

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Statements 44–47: `tcatWs` built (its `FILLER` of 22 spaces). -/
theorem run_seg44 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J44 g g.args σ0 fr σ)
    (c45 : cuts.lookup 45 = none) (c46 : cuts.lookup 46 = none) (c47 : cuts.lookup 47 = none)
    (c48 : cuts.lookup 48 = some (J48 g g.args σ0)) :
    RunWPcX g σ0 cuts 44 fr σ := by
  obtain ⟨-, -, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, wA, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, f13, hH, hKX, hXA, hg, hinits, hstat,
    hinit⟩ := h
  have hiC : σ.initOf "Cbtrn02c$TranCatBalRecord" = .done := by rw [initOf_of_inits' hinits]; exact i6
  have hlt : wA < σ.next := by
    obtain ⟨-, -, fsA, hAh, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hAh
  have hg' := Hide.intro hg
  clear hg
  unfold RunWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorTCSig, ctorTCSpec,
    fields_get_cons, fields_get_nil]
  rename_i vR σC hC
  rename State.heap _ _ = some (Obj.str (spJ 22)) => hs22
  obtain ⟨hC1, hC2, hC3, hC4, hC5, -⟩ := hC σ.next _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl (by chain_simp)
  have hne : w ≠ σ.next := ne_of_heap_str_plain hs22 (by chain_simp)
  have hgC : Grows σ σC := by grows_tac
  obtain ⟨hP, hX, hA⟩ := Hide.elim hH
  refine ⟨lC, lK, wX, wA, σ.next, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    Hide.intro ⟨hP.grows hgC, hX.grows hgC, hA.grows hgC,
      wsobj_of_setFields hC1 (by decide) (by simp), ⟨_, .ref w, hC1, ?_, w, rfl, ?_⟩⟩,
    hKX, hXA, hlt, grows_trans (Hide.elim hg') hgC, hC4, hC5, ?_⟩
  any_goals (frame_simp [f32, f0, f16, f31, f8, f11, f12, f6, f13]; done)
  · simp (config := { decide := true }) only [setFields, Fields.get_set, ite_true, ite_false,
      reduceIte]
  · rw [cp037Str_sp]
    chain_simp
  · rw [initOf_of_inits' hC4]

end EquivLean.Modernize.Cbtrn02c.Java
