import EquivLean.Modernize.Cbstm03a.Java.Term2.WriteTrans

/-!
# CBSTM03A → Java, termination: `writeTrans`'s contract

`writeTrans_ctermB`: `writeTrans` terminates on `writeTransSpecB`'s inputs (`writeTransSpec` with the transaction id
of at most `2^30` characters), given the contracts of `fix`, `fmtZ`, `star` (validity and termination); `stmt` and
`html` are inlined.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

open Term2

theorem writeTrans_ctermB (hfix : ContractOK Gen.prog fixSig fixSpecI)
    (hfixT : ContractTerm Gen.prog fixSig fixSpecI) (hz : ContractOK Gen.prog fmtZSig fmtZSpec)
    (hzT : ContractTerm Gen.prog fmtZSig fmtZSpec) (hs : ContractOK Gen.prog starSig starSpec)
    (hsT : ContractTerm Gen.prog starSig starSpec) : ContractTerm Gen.prog writeTransSig writeTransSpecB := by
  have hok : ∀ p ∈ wtCallees, ContractOK Gen.prog p.1 p.2 := by
    simp only [wtCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hfix, hz, hs⟩
  have htm : ∀ p ∈ wtCallees, ContractTerm Gen.prog p.1 p.2 := by
    simp only [wtCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hfixT, hzT, hsT⟩
  have ht : ∀ args σ, writeTransSpecB.pre args σ → MTerm Gen.prog writeTransRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok hok) (Contracts.term_of_ok htm _ _) writeTrans_tvc
  jcontract_term [ht]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.writeTrans_ctermB
