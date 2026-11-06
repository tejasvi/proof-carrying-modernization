import EquivLean.Modernize.Cbstm03a.Java.Term2.Defs

/-!
# CBSTM03A → Java, termination: an extra cut point on a termination path

`callWPT` is monotone in its continuation (`callWPT_mono`), so `bodyWP` with it is monotone in its fuel
(`bodyWP_fuelT`). A path proved up to an extra statement `p0` (assertion `A`, not a cut point of `I`) and the paths
from `p0` under `A` give the path without the extra cut point (`bodyWP_cutT`): the assertion is stated about the
values at `p0` (e.g. a slot offset as a variable instead of the term `jvc` computed it as).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

variable {P : Program}

theorem callWPT_mono (Γ : SpecEnv) :
    ∀ d sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) →
      callWPT P Γ d sig c args σ K → callWPT P Γ d sig c args σ K' := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K K' hK h
    unfold callWPT at h ⊢
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h ⊢
    all_goals first
      | exact h.elim
      | exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun o ho => hK o (h.2.2.2.2.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K K' hK h
    unfold callWPT at h ⊢
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ] at h ⊢
      · exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun o ho => hK o (h.2.2.2.2.2 o ho)⟩
    | none =>
      cases c with
      | method m =>
        simp only [hΓ] at h ⊢
        cases hb : m.decl.body with
        | none => simp only [hb] at h ⊢; exact hK _ h
        | some b =>
          simp only [hb] at h ⊢
          exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
      | virtual c =>
        simp only [hΓ] at h ⊢
        cases hsel : P.selectVirtual c sig.sub with
        | jimple m =>
          simp only [hsel] at h ⊢
          cases hb : m.decl.body with
          | none => simp only [hb] at h ⊢; exact hK _ h
          | some b =>
            simp only [hb] at h ⊢
            exact bodyWP_le ih b [] K K' hK inlineFuel 0 _ σ h
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
                  obtain ⟨hc, h⟩ := h
                  refine ⟨hc, ?_⟩
                  cases hp : Native.plainInst P sig lc a c fs rest σ with
                  | none => simp only [hp] at h ⊢; exact hK _ h
                  | some r =>
                    simp only [hp] at h ⊢
                    exact wpR_le ih r _ _ (fun ev h1 => hK _ h1) h
                | _ => simp only [hh] at h
            | _ => exact h.elim
        | none why =>
          simp only [hsel] at h ⊢
          exact ⟨h.1, hK _ h.2⟩

theorem bodyWP_fuelT {Γ : SpecEnv} {d : Nat} {b : Body} {I : Cuts} {Post : Outcome → Prop} :
    ∀ n m pc fr σ, n ≤ m → bodyWP P (callWPT P Γ d) b I Post n pc fr σ →
      bodyWP P (callWPT P Γ d) b I Post m pc fr σ := by
  intro n
  induction n with
  | zero => intro m pc fr σ _ h; simp only [bodyWP] at h
  | succ n ih =>
    intro m pc fr σ hnm h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [bodyWP] at h ⊢
    refine wpR_le (callWPT_mono Γ d) _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact ih m pc' fr' σ' (by omega)

theorem bodyWP_cutT {Γ : SpecEnv} {d : Nat} {b : Body} {I : Cuts} {Post : Outcome → Prop} {p0 m : Nat}
    {A : Frame → State → Prop} (h0 : I.lookup p0 = none)
    (hA : ∀ fr σ, A fr σ → bodyWP P (callWPT P Γ d) b I Post m p0 fr σ) :
    ∀ n pc fr σ, bodyWP P (callWPT P Γ d) b ((p0, A) :: I) Post n pc fr σ →
      bodyWP P (callWPT P Γ d) b I Post (n + m) pc fr σ := by
  intro n
  induction n with
  | zero => intro pc fr σ h; simp only [bodyWP] at h
  | succ n ih =>
    intro pc fr σ h
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [bodyWP] at h ⊢
    refine wpR_le (callWPT_mono Γ d) _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup_cons]
      by_cases hp : pc' = p0
      · subst hp
        simp only [beq_self_eq_true, h0]
        intro hA'
        exact bodyWP_fuelT m (n + m) _ _ _ (by omega) (hA _ _ hA')
      · have hne : (pc' == p0) = false := by simpa using hp
        simp only [hne]
        cases I.lookup pc' with
        | some B => exact id
        | none => exact ih pc' fr' σ'

end EquivLean.Modernize.Cbstm03a.Java.Term2
