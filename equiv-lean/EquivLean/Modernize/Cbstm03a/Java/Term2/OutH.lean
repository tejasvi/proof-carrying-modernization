import EquivLean.Modernize.Cbstm03a.Java.Term2.Out

/-!
# CBSTM03A → Java, termination: `stmt` and `html` on the heap (callee contracts for `writeTrans`, `createStatement`)

`stmtSpecH`, `htmlSpecH`: the precondition asks for the `Result` object and its list as heap facts (they carry over
allocations and the other calls' frames without a relation to re-establish), the postcondition is a frame: only the
list changes, and it stays an `ArrayList`. Proved here (`MethodVC` with `fixSpecI`), with their termination.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

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
  have hs : Sat Gen.prog stmtRef stmtSpecH := MethodVC.sat_of_valid (Contracts.valid_of_ok (outCallees_ok hfix)) stmtH_vc
  jcontract_ok [hs]

theorem htmlH_ok (hfix : ContractOK Gen.prog fixSig fixSpecI) : ContractOK Gen.prog htmlSig htmlSpecH := by
  have hs : Sat Gen.prog htmlRef htmlSpecH := MethodVC.sat_of_valid (Contracts.valid_of_ok (outCallees_ok hfix)) htmlH_vc
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

end EquivLean.Modernize.Cbstm03a.Java.Term2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.stmtH_ok
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.htmlH_ok
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.stmtH_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.htmlH_cterm
