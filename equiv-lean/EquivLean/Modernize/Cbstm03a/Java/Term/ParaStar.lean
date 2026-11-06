import EquivLean.Modernize.Cbstm03a.Java.Term.App

/-!
# CBSTM03A → Java, termination: `para`, `star`

No loops: a new builder, `app` calls (`appSpecT`), `toString`, `fix` (`fixSpecT`). Direct termination VCs (`TermVC`,
no cut point), postcondition `True`. Precondition: two non-null strings of `int` length, `Cbstm03a` initialized.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def paraSpecT : Spec :=
  ⟨fun args σ => ∃ pv fv, args = [pv, fv] ∧ StrArgN σ pv ∧ StrArgN σ fv ∧ InitA σ, fun _ _ _ => True⟩

def paraCalleesT : Contracts := [(appSig, appSpecT), (fixSig, fixSpecT)]

theorem paraCalleesT_ok : ∀ p ∈ paraCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [paraCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨app_okT, fix_okT⟩
theorem paraCalleesT_term : ∀ p ∈ paraCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [paraCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨app_ctermT, fix_ctermT⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem para_tvcT : TermVC Gen.prog paraCalleesT.env (fun _ => 0) 1 0 paraRef paraSpecT [] 40 := by
  set_option jimple.modelContracts true in
  jterm [ite_nat_ne, findHandler, paraSpecT, StrArgN, StrArg, paraCalleesT, appSig, appSpecT, fixSig, fixSpecT,
    Keeps, GrowsT, Grows, bAddr, capOf, bLenAt, InitA]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem star_tvcT : TermVC Gen.prog paraCalleesT.env (fun _ => 0) 1 0 starRef paraSpecT [] 40 := by
  set_option jimple.modelContracts true in
  jterm [ite_nat_ne, findHandler, paraSpecT, StrArgN, StrArg, paraCalleesT, appSig, appSpecT, fixSig, fixSpecT,
    Keeps, GrowsT, Grows, bAddr, capOf, bLenAt, InitA]

theorem para_termT : ∀ args σ, paraSpecT.pre args σ → MTerm Gen.prog paraRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Contracts.valid_of_ok paraCalleesT_ok)
    (Contracts.term_of_ok paraCalleesT_term _ _) para_tvcT
theorem star_termT : ∀ args σ, paraSpecT.pre args σ → MTerm Gen.prog starRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Contracts.valid_of_ok paraCalleesT_ok)
    (Contracts.term_of_ok paraCalleesT_term _ _) star_tvcT

set_option maxHeartbeats 4000000 in
theorem para_ctermT : ContractTerm Gen.prog paraSig paraSpecT := by jcontract_term [para_termT]
set_option maxHeartbeats 4000000 in
theorem star_ctermT : ContractTerm Gen.prog starSig paraSpecT := by jcontract_term [star_termT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.para_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.star_ctermT
