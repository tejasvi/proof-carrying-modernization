import EquivLean.Modernize.Cbstm03a.Java.Term2.Defs

/-!
# CBSTM03A → Java, termination: `stmt`, `html`, `abend`

No loops. `stmt`/`html` read the `Result`'s list, call `fix(s, 80)`/`fix(s, 100)` (`fixSpecI`) and add the result
to the list; `abend` adds three strings to the display list and sets `abended` (no calls).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- The callee of `stmt` and `html`. -/
def outCallees : Contracts := [(fixSig, fixSpecI)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem stmt_tvc : TermVC Gen.prog outCallees.env (fun _ => 0) 1 0 stmtRef stmtSpec [] 30 := by
  jterm [stmtSpec, outCallees, fixSig, fixSpecI, ResAtL, ListAt, StrOk]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem html_tvc : TermVC Gen.prog outCallees.env (fun _ => 0) 1 0 htmlRef htmlSpec [] 30 := by
  jterm [htmlSpec, outCallees, fixSig, fixSpecI, ResAtL, ListAt, StrOk]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem abend_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 abendRef abendSpec [] 40 := by
  jterm [abendSpec, ResAtL, ListAt]

theorem outCallees_ok (h : ContractOK Gen.prog fixSig fixSpecI) : ∀ p ∈ outCallees, ContractOK Gen.prog p.1 p.2 := by
  simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact h

theorem outCallees_term (h : ContractTerm Gen.prog fixSig fixSpecI) :
    ∀ p ∈ outCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact h

theorem abend_term : ∀ args σ, abendSpec.pre args σ → MTerm Gen.prog abendRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) abend_tvc

end EquivLean.Modernize.Cbstm03a.Java.Term2

namespace EquivLean.Modernize.Cbstm03a.Java

open Term2

/-- **`stmt` terminates**, given `fix`'s contract (validity and termination). -/
theorem stmt_cterm (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI) :
    ContractTerm Gen.prog stmtSig stmtSpec := by
  have ht : ∀ args σ, stmtSpec.pre args σ → MTerm Gen.prog stmtRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (outCallees_ok hfix)) (Contracts.term_of_ok (outCallees_term hfixT) _ _)
      stmt_tvc
  jcontract_term [ht]

/-- **`html` terminates**, given `fix`'s contract (validity and termination). -/
theorem html_cterm (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI) :
    ContractTerm Gen.prog htmlSig htmlSpec := by
  have ht : ∀ args σ, htmlSpec.pre args σ → MTerm Gen.prog htmlRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (outCallees_ok hfix)) (Contracts.term_of_ok (outCallees_term hfixT) _ _)
      html_tvc
  jcontract_term [ht]

set_option maxHeartbeats 4000000 in
/-- **`abend` terminates** (no calls). -/
theorem abend_cterm : ContractTerm Gen.prog abendSig abendSpec := by jcontract_term [abend_term]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.stmt_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.html_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.abend_cterm
