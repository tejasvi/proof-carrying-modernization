import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2

/-!
# CBTRN02C → Java: `updateTcatbal`

`updateTcatbal(r, d, xrefWs, tcatWs, tcatData)` with key (account of `xrefWs`, type and category of
`d`), `j` the first index of the key in `tcatData`:
* `j < 0`: displays the missing key, sets `tcatWs` to the key with balance `amount % 10^11`
  (`FILLER` unchanged), appends a copy to `tcatData` and another to `r.tcatbalFileWrites`;
* `j ≥ 0`: copies record `j` into `tcatWs`, adds the amount to its balance (`% 10^11`), replaces
  record `j` by a copy and appends another copy to `r.tcatbalFileRewrites`.
The second search after the update finds the same index (the domain's paths never abend).
Postconditions are functions of the state at the call.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The value of field `k` of the object at `a`. -/
def fld (σ : State) (a : Addr) (k : FieldKey) : Value := (Fields.get (fieldsOf σ a) k).getD .null

/-- The `long` in field `k` of the object at `a`. -/
def lng (σ : State) (a : Addr) (k : FieldKey) : I64 :=
  match fld σ a k with
  | .long x => x
  | _ => 0

/-- The address of a reference value. -/
def objOf (v : Value) : Addr :=
  match v with
  | .ref a => a
  | _ => 0

abbrev tcBalKey : FieldKey := ("Cbtrn02c$TranCatBalRecord", "tranCatBal")
abbrev tcFillKey : FieldKey := ("Cbtrn02c$TranCatBalRecord", "filler1")
abbrev dispKey : FieldKey := ("Cbtrn02c$Result", "displays")
abbrev cwKey : FieldKey := ("Cbtrn02c$Result", "tcatbalFileWrites")
abbrev crKey : FieldKey := ("Cbtrn02c$Result", "tcatbalFileRewrites")
abbrev dTypeKey : FieldKey := ("Cbtrn02c$DalytranRecord", "dalytranTypeCd")
abbrev dCatKey : FieldKey := ("Cbtrn02c$DalytranRecord", "dalytranCatCd")
abbrev dAmtKey : FieldKey := ("Cbtrn02c$DalytranRecord", "dalytranAmt")
abbrev xAcctKey : FieldKey := ("Cbtrn02c$CardXrefRecord", "xrefAcctId")

/-- The display line for a missing category key. -/
def noCatJ (acct : I64) (ty : JStr) (cd : I64) : JStr :=
  JStr.ofString "TCATBAL record not found for key : " ++ zpadJ acct.toInt.natAbs 11 ++ ty ++
    zpadJ cd.toInt.natAbs 4 ++ JStr.ofString ".. Creating."

def findTcatbalSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "findTcatbal", [.cls "java.util.List", .prim .long, .cls "java.lang.String", .prim .long]⟩
set_option maxHeartbeats 0 in
theorem findTcatbalF_ok : ContractOK Gen.prog findTcatbalSig findTcatbalSpecF := by
  jcontract_ok [findTcatbalF_sat]

def copyTcatSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "Cbtrn02c$TranCatBalRecord", "copyTcat", [.cls "Cbtrn02c$TranCatBalRecord"]⟩
set_option maxHeartbeats 0 in
theorem copyTcatF_ok : ContractOK Gen.prog copyTcatSig copyTcatSpecF := by jcontract_ok [copyTcatF_sat]

def assignTcatSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "assignTcat", [.cls "Cbtrn02c$TranCatBalRecord", .cls "Cbtrn02c$TranCatBalRecord"]⟩
set_option maxHeartbeats 0 in
theorem assignTcatF_ok : ContractOK Gen.prog assignTcatSig assignTcatSpecF := by
  jcontract_ok [assignTcatF_sat]

def spacesSig : MethodSig := ⟨"Cbtrn02c", .cls "java.lang.String", "spaces", [.prim .int]⟩
theorem spaces_sat : Sat Gen.prog spacesRef spacesSpec := spaces_vc.sat
set_option maxHeartbeats 0 in
theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpec := by jcontract_ok [spaces_sat]

abbrev updateTcatbalRef : MethodRef :=
  Gen.Cbtrn02c.«updateTcatbal(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,Cbtrn02c$CardXrefRecord,Cbtrn02c$TranCatBalRecord,java.util.List)».ref

def utCallees : Contracts :=
  [(findTcatbalSig, findTcatbalSpecF), (padNumSig, padNumSpec), (assignTcatSig, assignTcatSpecF),
   (spacesSig, spacesSpec), (copyTcatSig, copyTcatSpecF), (abendSig, abendSpec)]

/-- What `updateTcatbal` reads and needs. -/
def UtPre (σ : State) (r d wX wC lC : Addr) : Prop :=
  ∃ (fsR fsd fsX fsC : List (FieldKey × Value)) (lD lCW lCR sty : Addr) (tyS : JStr)
    (cd amt acct : I64) (xs ds ws rs : List Value) (m mD mW mR : Nat),
    σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧ Fields.get fsR dispKey = some (.ref lD) ∧
    Fields.get fsR cwKey = some (.ref lCW) ∧ Fields.get fsR crKey = some (.ref lCR) ∧
    σ.heap d = some (.plain "Cbtrn02c$DalytranRecord" fsd) ∧
    Fields.get fsd dTypeKey = some (.ref sty) ∧ σ.heap sty = some (.str tyS) ∧
    tyS.length < 2147483648 ∧
    Fields.get fsd dCatKey = some (.long cd) ∧ Fields.get fsd dAmtKey = some (.long amt) ∧
    σ.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX) ∧ Fields.get fsX xAcctKey = some (.long acct) ∧
    σ.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC) ∧ AllSome tcKeys fsC ∧
    σ.heap lC = some (.list .arrayList xs m) ∧ TcatShapes σ xs ∧ xs.length < 2147483647 ∧
    (∀ v ∈ xs, v ≠ .ref wC) ∧
    (∀ v ∈ xs, ∃ y fs b, v = .ref y ∧ σ.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧
      AllSome tcKeys fs ∧ Fields.get fs tcBalKey = some (.long b)) ∧
    σ.heap lD = some (.list .arrayList ds mD) ∧ σ.heap lCW = some (.list .arrayList ws mW) ∧
    σ.heap lCR = some (.list .arrayList rs mR) ∧ [lD, lCW, lCR, lC].Nodup ∧
    -9223372036854775808 < acct.toInt ∧ -9223372036854775808 < cd.toInt ∧
    σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$TranCatBalRecord" = .done

/-- The key's first index in `tcatData`. -/
def utIdx (σ : State) (d wX lC : Addr) : Int :=
  firstIdx (tcMatch σ (lng σ wX xAcctKey) (argText σ (fld σ d dTypeKey)) (lng σ d dCatKey)) (listOf σ lC)

def updateTcatbalSpec : Spec := Spec.of
  (fun args σ => ∃ (r d wX wC lC : Addr), args = [.ref r, .ref d, .ref wX, .ref wC, .ref lC] ∧
     UtPre σ r d wX wC lC)
  (fun args σ r' σ' => ∀ (r d wX wC lC : Addr), args = [.ref r, .ref d, .ref wX, .ref wC, .ref lC] →
     r' = some (.int 0) ∧
     (utIdx σ d wX lC < 0 →
       ∃ (sD y1 y2 : Addr) (fsC' fs1 fs2 : List (FieldKey × Value)) (m1 m2 m3 : Nat),
         σ'.heap (refField σ r dispKey) =
           some (.list .arrayList (listOf σ (refField σ r dispKey) ++ [.ref sD]) m1) ∧
         σ'.heap sD = some (.str (noCatJ (lng σ wX xAcctKey) (argText σ (fld σ d dTypeKey))
           (lng σ d dCatKey))) ∧
         σ'.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC') ∧
         Fields.get fsC' tcAcctKey = some (.long (lng σ wX xAcctKey)) ∧
         Fields.get fsC' tcTypeKey = some (fld σ d dTypeKey) ∧
         Fields.get fsC' tcCdKey = some (.long (lng σ d dCatKey)) ∧
         Fields.get fsC' tcBalKey = some (.long ((0#64 + lng σ d dAmtKey).srem 100000000000#64)) ∧
         Fields.get fsC' tcFillKey = Fields.get (fieldsOf σ wC) tcFillKey ∧
         σ'.heap lC = some (.list .arrayList (listOf σ lC ++ [.ref y1]) m2) ∧
         σ'.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1) ∧
         SameFields tcKeys fs1 fsC' ∧
         σ'.heap (refField σ r cwKey) =
           some (.list .arrayList (listOf σ (refField σ r cwKey) ++ [.ref y2]) m3) ∧
         σ'.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2) ∧
         SameFields tcKeys fs2 fsC' ∧
         σ.next ≤ y1 ∧ σ.next ≤ y2 ∧ y1 ≠ y2 ∧ σ.next ≤ sD ∧
         FrameS σ σ' [wC, lC, refField σ r dispKey, refField σ r cwKey]) ∧
     (0 ≤ utIdx σ d wX lC →
       ∃ (y1 y2 : Addr) (fsA fs1 fs2 : List (FieldKey × Value)) (m2 m3 : Nat),
         (∀ k ∈ tcKeys, Fields.get fsA k =
           Fields.get (fieldsOf σ (objOf ((listOf σ lC).getD (utIdx σ d wX lC).toNat .null))) k) ∧
         σ'.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" (Fields.set fsA tcBalKey
           (.long ((lng σ (objOf ((listOf σ lC).getD (utIdx σ d wX lC).toNat .null)) tcBalKey +
             lng σ d dAmtKey).srem 100000000000#64)))) ∧
         σ'.heap lC = some (.list .arrayList ((listOf σ lC).set (utIdx σ d wX lC).toNat (.ref y1)) m2) ∧
         σ'.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1) ∧
         SameFields tcKeys fs1 (Fields.set fsA tcBalKey
           (.long ((lng σ (objOf ((listOf σ lC).getD (utIdx σ d wX lC).toNat .null)) tcBalKey +
             lng σ d dAmtKey).srem 100000000000#64))) ∧
         σ'.heap (refField σ r crKey) =
           some (.list .arrayList (listOf σ (refField σ r crKey) ++ [.ref y2]) m3) ∧
         σ'.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2) ∧
         SameFields tcKeys fs2 (Fields.set fsA tcBalKey
           (.long ((lng σ (objOf ((listOf σ lC).getD (utIdx σ d wX lC).toNat .null)) tcBalKey +
             lng σ d dAmtKey).srem 100000000000#64))) ∧
         σ.next ≤ y1 ∧ σ.next ≤ y2 ∧ y1 ≠ y2 ∧ FrameS σ σ' [wC, lC, refField σ r crKey]) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

end EquivLean.Modernize.Cbtrn02c.Java
