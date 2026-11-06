import EquivLean.Modernize.Cbstm03a.Java.Iface2
import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03a.Java.Iface3
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, termination of `createStatement`: `stmt`/`html` on the heap, virtual cuts (namespace `…Java.Thin3`)

Copied from cbA-term2 (`CbATerm2.Out`, `CbATerm2.OutH`, `CbATerm2.Cut`, r4/agents/cbA_term2):
* `stmtSpecH`, `htmlSpecH`: `stmt`/`html` with the `Result` object and its list as heap facts in the precondition,
  a frame as the postcondition (only the list changes, it stays an `ArrayList`), with their validity and
  termination given `fix`'s;
* `bodyWP_cutT`: an extra cut point on a termination path (`callWPT` is monotone in its continuation, so `bodyWP`
  with it is monotone in its fuel).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-! ## Virtual cut points on termination paths -/

section CutT
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

/-- A virtual cut point `p0` with assertion `A`: the paths to `p0` establish `A`, the paths from `p0` continue. -/
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

end CutT

/-! ## `stmt` and `html` on the heap -/

/-- The callee of `stmt` and `html`. -/
def outCallees : Contracts := [(fixSig, fixSpecI)]

theorem outCallees_ok (h : ContractOK Gen.prog fixSig fixSpecI) : ∀ p ∈ outCallees, ContractOK Gen.prog p.1 p.2 := by
  simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact h

theorem outCallees_term (h : ContractTerm Gen.prog fixSig fixSpecI) :
    ∀ p ∈ outCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact h

/-- `stmt(res, s)` on the heap. -/
def stmtSpecH : Spec := Spec.of
  (fun args σ => ∃ (res ls : Addr) (fs : List (FieldKey × Value)) (xs : List Value) (m : Nat) (s : Value),
     args = [.ref res, s] ∧ σ.heap res = some (.plain resC fs) ∧
     Fields.get fs (resC, "stmtFileWrites") = some (.ref ls) ∧ σ.heap ls = some (.list .arrayList xs m) ∧
     StrOk σ s ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ls : Addr) (fs : List (FieldKey × Value)) (s : Value), args = [.ref res, s] →
     σ.heap res = some (.plain resC fs) → Fields.get fs (resC, "stmtFileWrites") = some (.ref ls) →
     r = none ∧ Keeps (· = ls) σ σ' ∧ (∃ xs m, σ'.heap ls = some (.list .arrayList xs m)) ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `html(res, s)` on the heap. -/
def htmlSpecH : Spec := Spec.of
  (fun args σ => ∃ (res lh : Addr) (fs : List (FieldKey × Value)) (xs : List Value) (m : Nat) (s : Value),
     args = [.ref res, s] ∧ σ.heap res = some (.plain resC fs) ∧
     Fields.get fs (resC, "htmlFileWrites") = some (.ref lh) ∧ σ.heap lh = some (.list .arrayList xs m) ∧
     StrOk σ s ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res lh : Addr) (fs : List (FieldKey × Value)) (s : Value), args = [.ref res, s] →
     σ.heap res = some (.plain resC fs) → Fields.get fs (resC, "htmlFileWrites") = some (.ref lh) →
     r = none ∧ Keeps (· = lh) σ σ' ∧ (∃ xs m, σ'.heap lh = some (.list .arrayList xs m)) ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem stmtH_vc : MethodVC Gen.prog outCallees.env 0 stmtRef stmtSpecH [] 30 := by
  jverify [stmtSpecH, outCallees, fixSig, fixSpecI, Keeps, Grows, StrOk]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem htmlH_vc : MethodVC Gen.prog outCallees.env 0 htmlRef htmlSpecH [] 30 := by
  jverify [htmlSpecH, outCallees, fixSig, fixSpecI, Keeps, Grows, StrOk]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem stmtH_tvc : TermVC Gen.prog outCallees.env (fun _ => 0) 1 0 stmtRef stmtSpecH [] 30 := by
  jterm [stmtSpecH, outCallees, fixSig, fixSpecI, StrOk]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem htmlH_tvc : TermVC Gen.prog outCallees.env (fun _ => 0) 1 0 htmlRef htmlSpecH [] 30 := by
  jterm [htmlSpecH, outCallees, fixSig, fixSpecI, StrOk]

theorem stmtH_ok (hfix : ContractOK Gen.prog fixSig fixSpecI) : ContractOK Gen.prog stmtSig stmtSpecH := by
  have hs : Sat Gen.prog stmtRef stmtSpecH :=
    MethodVC.sat_of_valid (Contracts.valid_of_ok (outCallees_ok hfix)) stmtH_vc
  jcontract_ok [hs]

theorem htmlH_ok (hfix : ContractOK Gen.prog fixSig fixSpecI) : ContractOK Gen.prog htmlSig htmlSpecH := by
  have hs : Sat Gen.prog htmlRef htmlSpecH :=
    MethodVC.sat_of_valid (Contracts.valid_of_ok (outCallees_ok hfix)) htmlH_vc
  jcontract_ok [hs]

theorem stmtH_cterm (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI) :
    ContractTerm Gen.prog stmtSig stmtSpecH := by
  have ht : ∀ args σ, stmtSpecH.pre args σ → MTerm Gen.prog stmtRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (outCallees_ok hfix)) (Contracts.term_of_ok (outCallees_term hfixT) _ _)
      stmtH_tvc
  jcontract_term [ht]

theorem htmlH_cterm (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI) :
    ContractTerm Gen.prog htmlSig htmlSpecH := by
  have ht : ∀ args σ, htmlSpecH.pre args σ → MTerm Gen.prog htmlRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (outCallees_ok hfix)) (Contracts.term_of_ok (outCallees_term hfixT) _ _)
      htmlH_tvc
  jcontract_term [ht]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
