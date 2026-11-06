import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW

/-!
# CBTRN02C → Java: `writeTransaction`, and `abend` (never called)

`abend` is reached only on paths that the domain excludes: its contract has precondition
`False`, so each call site proves that its path is impossible.

`writeTransaction(r, tranWs, tranKeys)`: the id of `tranWs` is new (`firstIdx … = -1`), so it is
added to `tranKeys` and a copy of `tranWs` to `r.transactFileWrites`; returns `false`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev abendRef : MethodRef :=
  Gen.Cbtrn02c.«abend(Cbtrn02c$Result,java.lang.String,java.lang.String)».ref

/-- `abend` is never called on the domain. -/
def abendSpec : Spec := Spec.of (fun _ _ => False) (fun _ _ _ _ => True)

def abendSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "abend", [.cls "Cbtrn02c$Result", .cls "java.lang.String", .cls "java.lang.String"]⟩

theorem abend_vc : MethodVC Gen.prog (fun _ => none) 0 abendRef abendSpec [] 10 := by
  jverify [abendSpec]

theorem abend_sat : Sat Gen.prog abendRef abendSpec := abend_vc.sat
set_option maxHeartbeats 0 in
theorem abend_ok : ContractOK Gen.prog abendSig abendSpec := by jcontract_ok [abend_sat]

def findKeySig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "findKey", [.cls "java.util.List", .cls "java.lang.String"]⟩
set_option maxHeartbeats 0 in
theorem findKeyF_ok : ContractOK Gen.prog findKeySig findKeySpecF := by jcontract_ok [findKeyF_sat]

def copyTranSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "Cbtrn02c$TranRecord", "copyTran", [.cls "Cbtrn02c$TranRecord"]⟩
set_option maxHeartbeats 0 in
theorem copyTranF_ok : ContractOK Gen.prog copyTranSig copyTranSpecF := by jcontract_ok [copyTranF_sat]

abbrev writeTransactionRef : MethodRef :=
  Gen.Cbtrn02c.«writeTransaction(Cbtrn02c$Result,Cbtrn02c$TranRecord,java.util.List)».ref

def wtCallees : Contracts := [(findKeySig, findKeySpecF), (copyTranSig, copyTranSpecF), (abendSig, abendSpec)]

def writeTransactionSpec : Spec := Spec.of
  (fun args σ => ∃ (r wT lK : Addr) (fsR : List (FieldKey × Value)) (lT : Addr)
       (fsT : List (FieldKey × Value)) (sId : Addr) (idcs : JStr) (ks : List Value) (mK : Nat)
       (ts : List Value) (mT : Nat),
     args = [.ref r, .ref wT, .ref lK] ∧ σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧
     Fields.get fsR ("Cbtrn02c$Result", "transactFileWrites") = some (.ref lT) ∧
     σ.heap wT = some (.plain "Cbtrn02c$TranRecord" fsT) ∧ AllSome trKeys fsT ∧
     Fields.get fsT ("Cbtrn02c$TranRecord", "tranId") = some (.ref sId) ∧
     σ.heap sId = some (.str idcs) ∧ σ.heap lK = some (.list .arrayList ks mK) ∧
     ks.length < 2147483648 ∧ StrShapes σ ks ∧
     firstIdx (fun v => strOfV σ v == some idcs) ks = -1 ∧
     σ.heap lT = some (.list .arrayList ts mT) ∧ lK ≠ lT ∧ σ.initOf "Cbtrn02c" = .done ∧
     σ.initOf "Cbtrn02c$TranRecord" = .done)
  (fun args σ r' σ' => ∀ (r wT lK : Addr) (fsR : List (FieldKey × Value)) (lT : Addr)
       (fsT : List (FieldKey × Value)) (sId : Addr) (ks : List Value) (mK : Nat) (ts : List Value)
       (mT : Nat),
     args = [.ref r, .ref wT, .ref lK] → σ.heap r = some (.plain "Cbtrn02c$Result" fsR) →
     Fields.get fsR ("Cbtrn02c$Result", "transactFileWrites") = some (.ref lT) →
     σ.heap wT = some (.plain "Cbtrn02c$TranRecord" fsT) →
     Fields.get fsT ("Cbtrn02c$TranRecord", "tranId") = some (.ref sId) →
     σ.heap lK = some (.list .arrayList ks mK) → σ.heap lT = some (.list .arrayList ts mT) →
     r' = some (.int 0) ∧
     ∃ (y : Addr) (fsy : List (FieldKey × Value)) (mK' mT' : Nat),
       σ'.heap lK = some (.list .arrayList (ks ++ [.ref sId]) mK') ∧
       σ'.heap lT = some (.list .arrayList (ts ++ [.ref y]) mT') ∧ σ.next ≤ y ∧
       σ'.heap y = some (.plain "Cbtrn02c$TranRecord" fsy) ∧
       SameFields trKeys fsy fsT ∧ FrameS σ σ' [lK, lT] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem writeTransaction_vc :
    MethodVC Gen.prog wtCallees.env 0 writeTransactionRef writeTransactionSpec [] 40 := by
  jverify [writeTransactionSpec, wtCallees, findKeySig, findKeySpecF, findKeySpec, copyTranSig,
    copyTranSpecF, abendSig, abendSpec, Grows, FrameS, argText, listOf, fieldsOf, strOfV]

end EquivLean.Modernize.Cbtrn02c.Java
