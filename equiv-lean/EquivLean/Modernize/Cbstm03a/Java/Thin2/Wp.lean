import EquivLean.Modernize.Cbstm03a.Java.Thin2.Lem

/-!
# CBSTM03A → Java: splitting a thin path at an intermediate statement

`callWPThin` is monotone in the continuation, so `bodyWP` is monotone in the fuel, and a cut point can be inserted
into the cut list (`bodyWP_cut`): a path that reaches the inserted statement `pm` continues by a lemma about the
paths from `pm`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Thin2

variable {P : Program}

/-- `callWPThin` is monotone in the continuation. -/
theorem callWPThin_mono (Γ : SpecEnv) :
    ∀ d sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) →
      callWPThin P Γ d sig c args σ K → callWPThin P Γ d sig c args σ K' := by
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

/-- More fuel: every path that ends within `n` statements ends within `m ≥ n`. -/
theorem bodyWP_fuel {H : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K')
    (b : Body) (I : Cuts) (Post : Outcome → Prop) :
    ∀ n m pc fr σ, n ≤ m → bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post m pc fr σ
  | 0, _, _, _, _, _, h => h.elim
  | n + 1, m, pc, fr, σ, hnm, h => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_fuel hH b I Post n m pc' fr' σ' (by omega)

/-- **Cut insertion**: paths checked against the cut list with `pm` added (assertion `A`), and the paths from
`pm` for every state satisfying `A`, give the paths against the original cut list. -/
theorem bodyWP_cut {H : Handler}
    (hH : ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K')
    (b : Body) (I : Cuts) (Post : Outcome → Prop) (pm : Nat) (hpm : I.lookup pm = none)
    (A : Frame → State → Prop) (m : Nat) (hA : ∀ fr σ, A fr σ → bodyWP P H b I Post m pm fr σ) :
    ∀ n pc fr σ, bodyWP P H b ((pm, A) :: I) Post n pc fr σ → bodyWP P H b I Post (n + m) pc fr σ
  | 0, _, _, _, h => h.elim
  | n + 1, pc, fr, σ, h => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [bodyWP] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup_cons]
      by_cases hp : pc' = pm
      · subst hp
        simp only [beq_self_eq_true, hpm]
        intro hA'
        exact bodyWP_fuel hH b I Post m (n + m) pc' fr' σ' (by omega) (hA fr' σ' hA')
      · have hb : (pc' == pm) = false := by simpa using hp
        simp only [hb]
        cases I.lookup pc' with
        | some A' => exact id
        | none => exact bodyWP_cut hH b I Post pm hpm A m hA n pc' fr' σ'

end EquivLean.Modernize.Cbstm03a.Java.Thin2
