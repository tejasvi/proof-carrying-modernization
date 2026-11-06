import EquivLean.Modernize.Cbact04c.JavaRunCtorSpecs

/-!
# CBACT04C → Java: the contracts of the record copies

`copyTcb`, `copyXref`, `copyAcct`, `copyDis`, `copyTran`: a fresh object of the record class
holding the same field values. The proofs are in `CopyProofs`.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- A copy of the object at `x` (class `cls`, fields `keys`): a fresh object of `cls` holding the
same values in `keys`. -/
def copySpec (cls : ClassName) (keys : List String) : Spec := Spec.of
  (fun args σ => ∃ x fs, args = [.ref x] ∧ σ.heap x = some (.plain cls fs) ∧
     (∀ k ∈ keys, ∃ v, Fields.get fs (cls, k) = some v) ∧ σ.initOf cls = .done)
  (fun args σ r σ' => ∀ x fs, args = [.ref x] → σ.heap x = some (.plain cls fs) →
     ∃ y fs', r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.plain cls fs') ∧
       (∀ k ∈ keys, Fields.get fs' (cls, k) = Fields.get fs (cls, k)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def keysTC : List String := ["trancatAcctId", "trancatTypeCd", "trancatCd", "tranCatBal", "filler1"]
def keysXC : List String := ["xrefCardNum", "xrefCustId", "xrefAcctId", "filler1"]
def keysAC : List String := ["acctId", "acctActiveStatus", "acctCurrBal", "acctCreditLimit",
  "acctCashCreditLimit", "acctOpenDate", "acctExpiraionDate", "acctReissueDate",
  "acctCurrCycCredit", "acctCurrCycDebit", "acctAddrZip", "acctGroupId", "filler1"]
def keysDC : List String := ["disAcctGroupId", "disTranTypeCd", "disTranCatCd", "disIntRate", "filler1"]
def keysRC : List String := ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt",
  "tranMerchantId", "tranMerchantName", "tranMerchantCity", "tranMerchantZip", "tranCardNum",
  "tranOrigTs", "tranProcTs", "filler1"]

abbrev copyTcbRef : MethodRef := Gen.Cbact04c.«copyTcb(Cbact04c$TranCatBalRecord)».ref
abbrev copyXrefRef : MethodRef := Gen.Cbact04c.«copyXref(Cbact04c$CardXrefRecord)».ref
abbrev copyAcctRef : MethodRef := Gen.Cbact04c.«copyAcct(Cbact04c$AccountRecord)».ref
abbrev copyDisRef : MethodRef := Gen.Cbact04c.«copyDis(Cbact04c$DisGroupRecord)».ref
abbrev copyTranRef : MethodRef := Gen.Cbact04c.«copyTran(Cbact04c$TranRecord)».ref

def copyTcbSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$TranCatBalRecord", name := "copyTcb",
    params := [.cls "Cbact04c$TranCatBalRecord"] }
def copyXrefSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$CardXrefRecord", name := "copyXref",
    params := [.cls "Cbact04c$CardXrefRecord"] }
def copyAcctSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$AccountRecord", name := "copyAcct",
    params := [.cls "Cbact04c$AccountRecord"] }
def copyDisSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$DisGroupRecord", name := "copyDis",
    params := [.cls "Cbact04c$DisGroupRecord"] }
def copyTranSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$TranRecord", name := "copyTran",
    params := [.cls "Cbact04c$TranRecord"] }

end EquivLean.Modernize.Cbact04c.Java
