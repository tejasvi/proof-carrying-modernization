import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVR

/-!
# CBTRN02C → Java: `validateTran`

`validateTran(d, xrefFile, acctData, xrefWs, acctWs)` returns the model's reject reason of the
transaction (`vreason`: 100 no cross-reference, 101 no account, 103 expired, 102 over the limit,
0 valid), having copied the cross-reference into `xrefWs` and the account into `acctWs` (when found).
Only `xrefWs` and `acctWs` change.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

def findXrefSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "findXref", [.array (.cls "Cbtrn02c$CardXrefRecord"), .cls "java.lang.String"]⟩
set_option maxHeartbeats 0 in
theorem findXrefF_ok : ContractOK Gen.prog findXrefSig findXrefSpecF := by
  jcontract_ok [findXrefF_sat]

def findAccountSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "findAccount", [.array (.cls "Cbtrn02c$AccountRecord"), .prim .long]⟩
set_option maxHeartbeats 0 in
theorem findAccountF_ok : ContractOK Gen.prog findAccountSig findAccountSpecF := by
  jcontract_ok [findAccountF_sat]

def assignXrefSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "assignXref", [.cls "Cbtrn02c$CardXrefRecord", .cls "Cbtrn02c$CardXrefRecord"]⟩
set_option maxHeartbeats 0 in
theorem assignXrefF_ok : ContractOK Gen.prog assignXrefSig assignXrefSpecF := by
  jcontract_ok [assignXrefF_sat]

def assignAccountSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "assignAccount", [.cls "Cbtrn02c$AccountRecord", .cls "Cbtrn02c$AccountRecord"]⟩
set_option maxHeartbeats 0 in
theorem assignAccountF_ok : ContractOK Gen.prog assignAccountSig assignAccountSpecF := by
  jcontract_ok [assignAccountF_sat]

def compareEbcdicSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "compareEbcdic", [.cls "java.lang.String", .cls "java.lang.String"]⟩
theorem compareEbcdic_sat : Sat Gen.prog compareEbcdicRef compareEbcdicSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [ceCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact ebcdic_ok)) compareEbcdic_vc
set_option maxHeartbeats 0 in
theorem compareEbcdicF_ok : ContractOK Gen.prog compareEbcdicSig compareEbcdicSpecF := by
  jcontract_ok [compareEbcdicF_sat compareEbcdic_sat]

/-- The fields of the daily transaction `t` that `validateTran` reads. -/
def VtD (σ : State) (d : Addr) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (fsd : List (FieldKey × Value)) (sc so : Addr),
    σ.heap d = some (.plain "Cbtrn02c$DalytranRecord" fsd) ∧
    Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranCardNum") = some (.ref sc) ∧
    σ.heap sc = some (.str (cp037Str (Model.tCard t))) ∧
    Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranAmt") = some
      (.long (BitVec.ofInt 64 (Model.tAmt t))) ∧
    Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranOrigTs") = some (.ref so) ∧
    σ.heap so = some (.str (cp037Str (Model.tOrig t))) ∧ (Model.tOrig t).length = 26 ∧
    (Model.tAmt t).natAbs < 100000000000

abbrev validateTranRef : MethodRef :=
  Gen.Cbtrn02c.«validateTran(Cbtrn02c$DalytranRecord,Cbtrn02c$CardXrefRecord[],Cbtrn02c$AccountRecord[],Cbtrn02c$CardXrefRecord,Cbtrn02c$AccountRecord)».ref

def vtCallees : Contracts :=
  [(findXrefSig, findXrefSpecF), (findAccountSig, findAccountSpecF), (assignXrefSig, assignXrefSpecF),
   (assignAccountSig, assignAccountSpecF), (compareEbcdicSig, compareEbcdicSpecF)]

/-- The model facts `validateTran` relies on: the cross-references and accounts in the arrays. -/
def VtIn (σ : State) (xA aD wX wA : Addr) (vals2 accts : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ (etX : JType) (xsX : List Value) (etA : JType) (xsA : List Value),
    σ.heap xA = some (.array etX xsX) ∧ xsX.length < 2147483648 ∧
    (∀ v ∈ xsX, ∃ x, x ∈ vals2 ∧ XObj σ v x) ∧
    Forall2 (JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ) xsX vals2 ∧
    (∀ x ∈ vals2, CardXrefRecord.Valid x) ∧ (∀ v ∈ xsX, v ≠ .ref wX) ∧
    σ.heap aD = some (.array etA xsA) ∧ xsA.length < 2147483648 ∧
    (∀ v ∈ xsA, ∃ a, a ∈ accts ∧ AObj σ v a) ∧
    Forall2 (JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ) xsA accts ∧
    (∀ a ∈ accts, AccountRecord.Valid a) ∧ (∀ v ∈ xsA, v ≠ .ref wA)

def validateTranSpec : Spec := Spec.of
  (fun args σ => ∃ (d xA aD wX wA : Addr) (t : List EquivLean.Cobol.Rec.FVal)
       (vals2 accts : List (List EquivLean.Cobol.Rec.FVal)) (fsX fsA : List (FieldKey × Value)),
     args = [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] ∧ VtD σ d t ∧ VtIn σ xA aD wX wA vals2 accts ∧
     σ.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX) ∧ (∀ k ∈ xrKeys, (Fields.get fsX k).isSome) ∧
     σ.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA) ∧ (∀ k ∈ acKeys, (Fields.get fsA k).isSome) ∧
     σ.initOf "Cbtrn02c" = .done)
  (fun args σ r σ' => ∀ (d xA aD wX wA : Addr), args = [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] →
     FrameS σ σ' [wX, wA] ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
     σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c" ∧
     (∃ fsX', σ'.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX') ∧
        ∀ k ∈ xrKeys, (Fields.get fsX' k).isSome) ∧
     (∃ fsA', σ'.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA') ∧
        ∀ k ∈ acKeys, (Fields.get fsA' k).isSome) ∧
     ∃ c : I32, r = some (.int c) ∧
       ∀ (t : List EquivLean.Cobol.Rec.FVal) (vals2 accts : List (List EquivLean.Cobol.Rec.FVal)),
         VtD σ d t → VtIn σ xA aD wX wA vals2 accts →
         c = BitVec.ofInt 32 (vreason vals2 accts t) ∧
         (vreason vals2 accts t = 0 → ∃ x a, Model.findXref vals2 (Model.tCard t) = some x ∧
           Model.findAcct accts (Model.xAcct x) = some a ∧
           JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ' (.ref wX) x ∧
           JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ' (.ref wA) a))

end EquivLean.Modernize.Cbtrn02c.Java
