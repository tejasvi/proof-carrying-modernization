import EquivLean.Modernize.Cbstm03a.Java.Run2.Defs

/-!
# Extra cut points inside a segment

`cut_intro`: a path explored with an extra cut point `c` (assertion `A`, `c` not a cut point of `I`) and the paths
from `c` under `A` give the paths without it (fuel added). The handler `callWP` is monotone in the continuation,
and more fuel never hurts.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

section
variable {P : Program}

/-- A handler monotone in the continuation. -/
def HMono (H : Handler) : Prop :=
  ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K'

theorem callWP_mono (Γ : SpecEnv) : ∀ d, HMono (callWP P Γ d) := by
  intro d
  induction d with
  | zero =>
    intro sig c args σ K K' hK h
    unfold callWP at h ⊢
    cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h ⊢
    all_goals first
      | exact h.elim
      | exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun o ho => hK o (h.2.2.2.2 o ho)⟩
  | succ d ih =>
    intro sig c args σ K K' hK h
    unfold callWP at h ⊢
    cases hΓ : Γ sig with
    | some S =>
      cases c <;> simp only [hΓ] at h ⊢
      · exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
      · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun o ho => hK o (h.2.2.2.2 o ho)⟩
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
          · trivial
          · cases v with
            | ref a =>
              simp only at h ⊢
              cases hh : σ.heap a with
              | none => trivial
              | some o =>
                cases o with
                | plain c' fs =>
                  simp only [hh] at h ⊢
                  intro hc
                  have h2 := h hc
                  cases hp : Native.plainInst P sig lc a c fs rest σ with
                  | none => simp only [hp] at h2 ⊢; exact hK _ h2
                  | some r =>
                    simp only [hp] at h2 ⊢
                    exact wpR_le ih r _ _ (fun ev hev => hK _ hev) h2
                | _ => trivial
            | _ => trivial
        | none why =>
          simp only [hsel] at h ⊢
          exact fun hc => hK _ (h hc)

theorem bodyWP_fuel {H : Handler} (hH : HMono H) (b : Body) (I : Cuts) (Post : Outcome → Prop) :
    ∀ n k pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post (n + k) pc fr σ
  | 0, _, _, _, _, h => by simp only [bodyWP] at h
  | n + 1, k, pc, fr, σ, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_fuel hH b I Post n k pc' fr' σ'

theorem bodyWP_fuel_le {H : Handler} (hH : HMono H) {b : Body} {I : Cuts} {Post : Outcome → Prop}
    {n n' : Nat} {pc : Nat} {fr : Frame} {σ : State} (hle : n ≤ n') (h : bodyWP P H b I Post n pc fr σ) :
    bodyWP P H b I Post n' pc fr σ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact bodyWP_fuel hH b I Post n k pc fr σ h

/-- An extra cut point `c` with assertion `A`, whose paths (with fuel `m`) are proved separately. -/
theorem cut_intro {H : Handler} (hH : HMono H) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (c : Nat) (A : Frame → State → Prop) (hc : I.lookup c = none) (m : Nat)
    (hA : ∀ fr σ, A fr σ → bodyWP P H b I Post m c fr σ) :
    ∀ n pc fr σ, bodyWP P H b ((c, A) :: I) Post n pc fr σ → bodyWP P H b I Post (n + m) pc fr σ
  | 0, _, _, _, h => by simp only [bodyWP] at h
  | n + 1, pc, fr, σ, h => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup_cons]
      by_cases hp : pc' = c
      · rw [hp]
        simp only [beq_self_eq_true, hc]
        intro hA'
        exact bodyWP_fuel_le hH (by omega) (hA fr' σ' hA')
      · have hb : (pc' == c) = false := by simpa using hp
        simp only [hb]
        cases I.lookup pc' with
        | some A' => exact id
        | none => exact cut_intro hH b I Post c A hc m hA n pc' fr' σ'

end

end EquivLean.Modernize.Cbstm03a.Java.Seg2
