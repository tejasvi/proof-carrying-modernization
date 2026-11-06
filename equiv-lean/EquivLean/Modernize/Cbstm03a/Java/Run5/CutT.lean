import EquivLean.Modernize.Cbstm03a.Java.Run5.Cut

/-!
# CBSTM03A → Java, `run`'s thin segments: the thin handler is monotone

`callWPThin_mono` (cbA-thin3's `CbAThin3.Cut`): with it `bodyWP_cut_insert` applies to the thin VC's paths.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

theorem callWPThin_mono (P : Program) (Γ : SpecEnv) : ∀ d, HMono (callWPThin P Γ d) := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K K' hK h
    unfold callWPThin at h ⊢
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h ⊢
    all_goals first
      | exact h.elim
      | exact fun o ho => hK o (h o ho)
      | exact ⟨h.1, fun o ho => hK o (h.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K K' hK h
    unfold callWPThin at h ⊢
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ] at h ⊢
      · exact fun o ho => hK o (h o ho)
      · exact ⟨h.1, fun o ho => hK o (h.2 o ho)⟩
    | none =>
      cases c with
      | method m =>
        simp only [hΓ] at h ⊢
        cases hb : m.decl.body with
        | none => simp only [hb] at h ⊢; exact hK _ h
        | some b => simp only [hb] at h ⊢; exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
      | virtual c =>
        simp only [hΓ] at h ⊢
        cases hsel : P.selectVirtual c sig.sub with
        | jimple m =>
          simp only [hsel] at h ⊢
          cases hb : m.decl.body with
          | none => simp only [hb] at h ⊢; exact hK _ h
          | some b => simp only [hb] at h ⊢; exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
        | native lc =>
          simp only [hsel] at h ⊢
          rcases args with _ | ⟨v, rest⟩
          · exact h.elim
          · cases v with
            | ref a =>
              simp only at h ⊢
              cases hh : σ.heap a with
              | none => simp only [hh] at h
              | some o =>
                cases o with
                | plain c' fs =>
                  simp only [hh] at h ⊢
                  obtain ⟨hc, h2⟩ := h
                  refine ⟨hc, ?_⟩
                  cases hp : Native.plainInst P sig lc a c fs rest σ with
                  | none => simp only [hp] at h2 ⊢; exact hK _ h2
                  | some r =>
                    simp only [hp] at h2 ⊢
                    exact wpR_le ih r _ _ (fun ev hev => hK _ hev) h2
                | _ => simp only [hh] at h
            | _ => exact h.elim
        | none why =>
          simp only [hsel] at h ⊢
          exact ⟨h.1, hK _ h.2⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg5
