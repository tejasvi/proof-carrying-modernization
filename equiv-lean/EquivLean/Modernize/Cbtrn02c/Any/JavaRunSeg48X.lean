import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL4

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem initOf_of_inits'' {σ σ0 : State} (h : σ.inits = σ0.inits) (c : ClassName) :
    σ.initOf c = σ0.initOf c := by
  simp only [State.initOf, h]

theorem ne_of_heap_str_plain' {σ : State} {a b : Addr} {t : JStr} {c : ClassName}
    {fs : List (FieldKey × Value)} (ha : σ.heap a = some (.str t)) (hb : σ.heap b = some (.plain c fs)) :
    a ≠ b := by
  rintro rfl; rw [ha] at hb; cases hb

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
/-- Statements 48–64: `tranWs` built (its `FILLER` of 20 spaces), the counters and flags set: the
main loop's first visit. -/
theorem run_seg48 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J48 g g.args σ0 fr σ)
    (c49 : cuts.lookup 49 = none) (c50 : cuts.lookup 50 = none) (c51 : cuts.lookup 51 = none)
    (c52 : cuts.lookup 52 = none) (c53 : cuts.lookup 53 = none) (c54 : cuts.lookup 54 = none)
    (c55 : cuts.lookup 55 = none) (c56 : cuts.lookup 56 = none) (c57 : cuts.lookup 57 = none)
    (c58 : cuts.lookup 58 = none) (c59 : cuts.lookup 59 = none) (c60 : cuts.lookup 60 = none)
    (c61 : cuts.lookup 61 = none) (c62 : cuts.lookup 62 = none) (c63 : cuts.lookup 63 = none)
    (c64 : cuts.lookup 64 = none) (c65 : cuts.lookup 65 = some (L65X g g.args σ0)) :
    RunWPcX g σ0 cuts 48 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨lC, lK, wX, wA, wC, ⟨f32, f0, f16, f31, f8, f11, f12⟩, f6, f13, f29, hH, hKX, hXA, hAC, hg,
    hinits, hstat, hinit⟩ := h
  have hiT : σ.initOf "Cbtrn02c$TranRecord" = .done := by rw [initOf_of_inits'' hinits]; exact i8
  have hlt : wC < σ.next := by
    obtain ⟨-, -, -, ⟨fsC, hCh, -⟩, -⟩ := Hide.elim hH
    exact State.lt_next_of_heap hCh
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  clear hg hin
  unfold RunWPcX
  jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorTRSig, ctorTRSpec,
    fields_get_cons, fields_get_nil]
  rename_i vR σT hT
  rename State.heap _ _ = some (Obj.str (spJ 20)) => hs20
  obtain ⟨hT1, hT2, hT3, hT4, hT5, -⟩ := hT σ.next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by chain_simp)
  have hne : w ≠ σ.next := ne_of_heap_str_plain' hs20 (by chain_simp)
  have hgT : Grows σ σT := by grows_tac
  obtain ⟨hP, hX, hA, hC, hFC⟩ := Hide.elim hH
  refine l65x_init (Hide.elim hin') ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hP.grows hgT) (hX.grows hgT) (hA.grows hgT) (hC.grows hgT)
    (wsobj_of_setFields hT1 (by decide) (by simp)) (hFC.grows hgT) ⟨_, .ref w, hT1, ?_, w, rfl, ?_⟩
    hKX hXA hAC hlt ⟨grows_trans (Hide.elim hg') hgT, hT4, hT5, ?_⟩
  any_goals (frame_simp [f32, f0, f16, f31, f8, f11, f12, f6, f13, f29]; done)
  · simp (config := { decide := true }) only [setFields, Fields.get_set, ite_true, ite_false]
  · rw [cp037Str_sp]
    chain_simp
  · rw [initOf_of_inits'' hT4]

end EquivLean.Modernize.Cbtrn02c.Java
