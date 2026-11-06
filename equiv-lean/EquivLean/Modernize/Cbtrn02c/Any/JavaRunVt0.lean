import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM0s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5b
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunDet

/-!
# CBTRN02C → Java: `validateTran`, the cut points

Statement 11 (after `assignXref`): the cross-reference found is in `xrefWs`, its account id read
as a `long`.  Statement 17 (after `assignAccount`): the account found is in `acctWs`, the fields
the checks read.  The model facts are stated for some reading of the inputs (`VtD`, `VtIn`); the
inputs are determined by the heap (`vtd_det`, `vtin_det`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem keysOf_xref2 : keysOf CardXrefRecord "Cbtrn02c$CardXrefRecord" = xrKeys := by decide
theorem keysOf_acct2 : keysOf AccountRecord "Cbtrn02c$AccountRecord" = acKeys := by decide

abbrev vtBodyC := Gen.Cbtrn02c.«validateTran(Cbtrn02c$DalytranRecord,Cbtrn02c$CardXrefRecord[],Cbtrn02c$AccountRecord[],Cbtrn02c$CardXrefRecord,Cbtrn02c$AccountRecord)»

/-- Statement 11: `xrefWs` holds the cross-reference of the transaction's card. -/
def vt11 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ d xA aD wX wA, args = [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] →
  ∃ (fsX' : List (FieldKey × Value)) (v : I64),
    fr.get 2 = some (.ref d) ∧ fr.get 1 = some (.ref xA) ∧ fr.get 0 = some (.ref aD) ∧
    fr.get 9 = some (.ref wX) ∧ fr.get 5 = some (.ref wA) ∧
    σ = σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX') ∧
    Fields.get fsX' ("Cbtrn02c$CardXrefRecord", "xrefAcctId") = some (.long v) ∧
    Hide (AllSome xrKeys fsX' ∧ ∃ t vals2 accts x, VtD σ0 d t ∧ VtIn σ0 xA aD wX wA vals2 accts ∧
      Model.findXref vals2 (Model.tCard t) = some x ∧
      JRecAt CardXrefRecord xrCls σ (.ref wX) x ∧ v = BitVec.ofInt 64 (Model.xAcct x))

/-- Statement 17: `acctWs` holds the account of the cross-reference; the fields the checks read. -/
def vt17 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ d xA aD wX wA, args = [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] →
  ∃ (fsX' fsA' : List (FieldKey × Value)) (cc cd lim : I64) (es : Addr) (exs : JStr),
    fr.get 2 = some (.ref d) ∧ fr.get 5 = some (.ref wA) ∧
    σ = (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
      (.plain "Cbtrn02c$AccountRecord" fsA') ∧
    Fields.get fsA' ("Cbtrn02c$AccountRecord", "acctCurrCycCredit") = some (.long cc) ∧
    Fields.get fsA' ("Cbtrn02c$AccountRecord", "acctCurrCycDebit") = some (.long cd) ∧
    Fields.get fsA' ("Cbtrn02c$AccountRecord", "acctCreditLimit") = some (.long lim) ∧
    Fields.get fsA' ("Cbtrn02c$AccountRecord", "acctExpiraionDate") = some (.ref es) ∧
    σ0.heap es = some (.str exs) ∧ es ≠ wX ∧ es ≠ wA ∧
    Hide (AllSome xrKeys fsX' ∧ AllSome acKeys fsA' ∧ ∃ t vals2 accts x a, VtD σ0 d t ∧
      VtIn σ0 xA aD wX wA vals2 accts ∧
      Model.findXref vals2 (Model.tCard t) = some x ∧ Model.findAcct accts (Model.xAcct x) = some a ∧
      JRecAt CardXrefRecord xrCls σ (.ref wX) x ∧ JRecAt AccountRecord acCls σ (.ref wA) a ∧
      cc = BitVec.ofInt 64 (Model.aCC a) ∧ cd = BitVec.ofInt 64 (Model.aCD a) ∧
      lim = BitVec.ofInt 64 (Model.aLimit a) ∧ exs = cp037Str (Model.aExp a))

def vtInv : Invariants := [(11, vt11), (17, vt17)]

/-- The postcondition of `validateTran`, folded. -/
def vtPostC (args : List Value) (σ0 : State) : Outcome → Prop := validateTranSpec.post args σ0

attribute [irreducible] vtPostC

/-- Symbolic execution of `validateTran`'s body from `pc` against the cut list `cuts`. -/
def VtWPc (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog vtCallees.env 0) vtBodyC cuts (vtPostC args σ0) 80 pc fr σ

attribute [irreducible] VtWPc

theorem VtWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    VtWPc args σ0 cuts pc fr σ = bodyWP Gen.prog (callWP Gen.prog vtCallees.env 0) vtBodyC cuts
      (validateTranSpec.post args σ0) 80 pc fr σ := by
  unfold VtWPc vtPostC
  rfl

end EquivLean.Modernize.Cbtrn02c.Java
