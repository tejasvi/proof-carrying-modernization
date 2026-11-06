import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java, `run`'s thin VC: virtual cut points (namespace `…Java.Thin3`)

`bodyWP_cut_insert`: a path may stop at a statement `k` that is no cut point, with an assertion `A`, when every
frame and state satisfying `A` continue from `k` (`bodyWP` with the original cut points). A segment proof then
restates at `k` the facts a callee's postcondition needs, about the state of the call itself. Needs the handler to
be monotone in its continuation (`callWPThin_mono`) and `bodyWP` monotone in the fuel.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

/-- A handler monotone in its continuation. -/
abbrev HMono (H : Handler) : Prop :=
  ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K'

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

theorem bodyWP_fuel_succ {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) :
    ∀ n pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post (n + 1) pc fr σ
  | 0, _, _, _, h => by rw [bodyWP_eq_false] at h; exact h.elim
  | n + 1, pc, fr, σ, h => by
    rw [bodyWP_succ] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_fuel_succ hH b I Post n pc' fr' σ'

theorem bodyWP_fuel_le {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) {n m : Nat} (hnm : n ≤ m) :
    ∀ pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post m pc fr σ := by
  induction hnm with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun pc fr σ h => bodyWP_fuel_succ hH b I Post _ pc fr σ (ih pc fr σ h)

/-- A virtual cut point `k` with assertion `A`: the paths to `k` establish `A`, the paths from `k` continue. -/
theorem bodyWP_cut_insert {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) (k : Nat) (hk : I.lookup k = none) (A : Frame → State → Prop) (n0 : Nat)
    (hA : ∀ fr σ, A fr σ → bodyWP P H b I Post n0 k fr σ) :
    ∀ n pc fr σ, bodyWP P H b ((k, A) :: I) Post n pc fr σ → bodyWP P H b I Post (n + n0) pc fr σ
  | 0, _, _, _, h => by rw [bodyWP_eq_false] at h; exact h.elim
  | n + 1, pc, fr, σ, h => by
    rw [show n + 1 + n0 = (n + n0) + 1 by omega, bodyWP_succ]
    rw [bodyWP_succ] at h
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup_cons]
      by_cases hp : pc' = k
      · subst hp
        simp only [beq_self_eq_true, hk]
        intro hA'
        exact bodyWP_fuel_le hH b I Post (Nat.le_add_left n0 n) _ _ _ (hA fr' σ' hA')
      · have hb : (pc' == k) = false := by simpa using hp
        simp only [hb]
        cases I.lookup pc' with
        | some A' => exact id
        | none => exact bodyWP_cut_insert hH b I Post k hk A n0 hA n pc' fr' σ'

end EquivLean.Modernize.Cbstm03a.Java.Thin3
