import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: the record-area constructor

From cut point 22: the constructor of the record area (spaces and zeros), the discarded
`spaces(16)`, the flags, up to the read loop (`J29` with no record read).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem cp037Str_spaces (n : Nat) : cp037Str (List.replicate n 64) = spJ n := by
  have h : cp037Unit 64 = space := by decide +kernel
  rw [cp037Str, List.map_replicate, h]
  rfl

theorem dal0_card : Model.strOf (Model.dal0.getD 10 default) = List.replicate 16 64 := rfl
theorem dal0_id : Model.strOf (Model.dal0.getD 0 default) = List.replicate 16 64 := rfl

theorem curT_zero (trans : List (List EquivLean.Cobol.Rec.FVal)) : curT trans 0 = Model.dal0 := by
  simp [curT]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg22 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State)
    (h : J22 a1 a3 a5 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 22 fr σ := by
  obtain ⟨r8, res, l, f10, f35, f4, f9, f11, f1, hr8, ⟨s20, f20, h20⟩, ⟨s21, f21, h21⟩,
    ⟨s22, f22, h22⟩, ⟨s23, f23, h23⟩, ⟨s24, f24, h24⟩, ⟨s25, f25, h25⟩, ⟨s26, f26, h26⟩,
    ⟨s27, f27, h27⟩, ⟨s28, f28, h28⟩, ⟨s29, f29, h29⟩, ⟨s30, f30, h30⟩, hres, hlist, hres0, hl0,
    hr80, hrl, hg, hinit⟩ := h
  obtain ⟨fsR, hR1, hR2, hR3⟩ := hres
  obtain ⟨ys, m, hl, hD⟩ := hlist
  have hrr8 : res ≠ r8 := by intro h; subst h; rw [hR1] at hr8; simp [dalCls] at hr8
  have hlr8 : l ≠ r8 := by intro h; subst h; rw [hl] at hr8; simp at hr8
  have hs20 : s20 ≠ r8 := by intro h; subst h; rw [h20] at hr8; simp at hr8
  have hs27 : s27 ≠ r8 := by intro h; subst h; rw [h27] at hr8; simp at hr8
  have hg' := Hide.intro hg
  have hR1' := Hide.intro hR1
  have hl' := Hide.intro hl
  clear hg hR1 hl
  unfold RunWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, spacesSpec, runArgs,
    inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, SpAt, dalCls, dalFields0]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  have hR1 := Hide.elim hR1'
  have hl := Hide.elim hl'
  have hg := Hide.elim hg'
  have hres_lt := State.lt_next_of_heap hR1
  have hl_lt := State.lt_next_of_heap hl
  refine ⟨0, false, .ref r8, res, l, ⟨?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_,
    by simp, ?_, ?_, ⟨fsR, ?_, hR2, hR3⟩, hres0, hl0, hrl, ?_, ?_⟩, ys, m, ?_, ?_⟩
  any_goals (trn_frame_simp [f10, f35, f4, f9, f11, f1, JInt.ofBool]; done)
  · rw [curT_zero]
    refine Hide.intro ⟨r8, dalFieldsAt s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30, s27, s20, rfl,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [dalFieldsAt, dalFields0, dalCls]
      trn_chain
    · simp (config := { decide := true }) only [dalFieldsAt, Fields.get_set, dalCls, ite_true,
        ite_false, reduceIte]
    · rw [dal0_card, cp037Str_spaces]; trn_chain
    · simp (config := { decide := true }) only [dalFieldsAt, Fields.get_set, dalCls, ite_true,
        ite_false, reduceIte]
    · rw [dal0_id, cp037Str_spaces]; trn_chain
  · trn_chain
  · obtain ⟨hg1, hg2⟩ := hg
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [State.next_setObj] at *
      jomega
    · trn_chain
  · trn_chain
  · trn_chain
  · rw [headL_zero]
    refine Hide.intro (forall2_mono (fun v t h => ?_) (Hide.elim hD))
    obtain ⟨x, rfl, hx⟩ := h
    have hxr8 : x ≠ r8 := by intro h; subst h; rw [hx] at hr8; simp at hr8
    have hx_lt := State.lt_next_of_heap hx
    exact ⟨x, rfl, by trn_chain⟩

end EquivLean.Modernize.Cbtrn01c.Java
