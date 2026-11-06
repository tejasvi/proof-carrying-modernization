import EquivLean.Modernize.Cbstm03a.Java.Run1.Lem

/-!
# A virtual cut point inside a segment

`bodyWP_vcut`: the paths from `pc` with fuel `n + m` against the cut list `I` follow from the paths with fuel `n`
against `I` with one more cut point `pc1` (assertion `A`, `pc1` not a key of `I`) and the paths from `pc1` with
fuel `m` for every state satisfying `A`. Used where `jvc` cannot carry a fact across a callee (a callee's
postcondition whose premises are heap facts of the call state).
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-- `callWP` is monotone in the continuation. -/
theorem callWP_mono (P : Program) (Γ : SpecEnv) :
    ∀ d sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) →
      callWP P Γ d sig c args σ K → callWP P Γ d sig c args σ K' := by
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
              | none => simp only [hh]
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
                | _ => simp only [hh]
            | _ => trivial
        | none why =>
          simp only [hsel] at h ⊢
          exact fun hc => hK _ (h hc)

/-- More fuel: every path that ends within `n` statements ends within `k ≥ n`. -/
theorem bodyWP_fuel {P : Program} {H : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K')
    (b : Body) (I : Cuts) (Post : Outcome → Prop) :
    ∀ n k pc fr σ, n ≤ k → bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post k pc fr σ
  | 0, _, _, _, _, _, h => h.elim
  | n + 1, k + 1, pc, fr, σ, hnk, h => by
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_fuel hH b I Post n k pc' fr' σ' (Nat.le_of_succ_le_succ hnk)

/-- **A virtual cut point** at `pc1`. -/
theorem bodyWP_vcut {P : Program} {H : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K')
    (b : Body) (I : Cuts) (Post : Outcome → Prop) (pc1 : Nat) (hI : I.lookup pc1 = none)
    (A : Frame → State → Prop) (m : Nat) (hA : ∀ fr σ, A fr σ → bodyWP P H b I Post m pc1 fr σ) :
    ∀ n pc fr σ, bodyWP P H b ((pc1, A) :: I) Post n pc fr σ → bodyWP P H b I Post (n + m) pc fr σ
  | 0, _, _, _, h => h.elim
  | n + 1, pc, fr, σ, h => by
    rw [Nat.add_right_comm]
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup]
      by_cases hp : pc' = pc1
      · subst hp
        simp only [beq_self_eq_true, hI]
        intro hA'
        exact bodyWP_fuel hH b I Post m (n + m) _ fr' σ' (Nat.le_add_left m n) (hA fr' σ' hA')
      · have hb : (pc' == pc1) = false := by simpa using hp
        simp only [hb]
        cases I.lookup pc' with
        | some A' => exact id
        | none => exact bodyWP_vcut hH b I Post pc1 hI A m hA n pc' fr' σ'

end EquivLean.Modernize.Cbstm03a.Java.Seg1
