import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW

/-!
# CBTRN02C → Java: `updateAccount`

`updateAccount(r, d, acctWs, acctData)`: the amount added to the balance and to the cycle credit
(amount ≥ 0) or debit, each `% 10^12` (`acctPostFs`); the account (found: `0 ≤ firstIdx …`)
replaced in `acctData` by a copy of `acctWs`, and another copy added to `r.accountFileRewrites`.
Only `acctWs`, `acctData` and that list change.  The postcondition is a function of the state at
the call.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

def copyAccountSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "Cbtrn02c$AccountRecord", "copyAccount", [.cls "Cbtrn02c$AccountRecord"]⟩
set_option maxHeartbeats 0 in
theorem copyAccountF_ok : ContractOK Gen.prog copyAccountSig copyAccountSpecF := by
  jcontract_ok [copyAccountF_sat]

def findAccountSig' : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "findAccount", [.array (.cls "Cbtrn02c$AccountRecord"), .prim .long]⟩

/-- The value of field `k` of the object at `a`. -/
def fld' (σ : State) (a : Addr) (k : FieldKey) : Value := (Fields.get (fieldsOf σ a) k).getD .null

/-- The `long` in field `k` of the object at `a`. -/
def lng' (σ : State) (a : Addr) (k : FieldKey) : I64 :=
  match fld' σ a k with
  | .long x => x
  | _ => 0

/-- A balance after posting `amt`: `(bal + amt) % 10^12`. -/
def balJ (bal amt : I64) : I64 := (bal + amt).srem 1000000000000#64

abbrev acBalKey : FieldKey := ("Cbtrn02c$AccountRecord", "acctCurrBal")
abbrev acCcKey : FieldKey := ("Cbtrn02c$AccountRecord", "acctCurrCycCredit")
abbrev acCdKey : FieldKey := ("Cbtrn02c$AccountRecord", "acctCurrCycDebit")
abbrev arKey : FieldKey := ("Cbtrn02c$Result", "accountFileRewrites")
abbrev dAmtKey' : FieldKey := ("Cbtrn02c$DalytranRecord", "dalytranAmt")

/-- The fields of `acctWs` after posting `amt`. -/
def acctPostFs (fs : List (FieldKey × Value)) (bal cc cdb amt : I64) : List (FieldKey × Value) :=
  if 0 ≤ amt.toInt then
    Fields.set (Fields.set fs acBalKey (.long (balJ bal amt))) acCcKey (.long (balJ cc amt))
  else Fields.set (Fields.set fs acBalKey (.long (balJ bal amt))) acCdKey (.long (balJ cdb amt))

abbrev updateAccountRef : MethodRef :=
  Gen.Cbtrn02c.«updateAccount(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,Cbtrn02c$AccountRecord,Cbtrn02c$AccountRecord[])».ref

def uaCallees : Contracts := [(findAccountSig', findAccountSpecF), (copyAccountSig, copyAccountSpecF)]

def updateAccountSpec : Spec := Spec.of
  (fun args σ => ∃ (r d wA aD : Addr) (fsR fsd fsA : List (FieldKey × Value)) (lAR : Addr)
       (amt bal cc cdb id : I64) (xsA : List Value) (ys : List Value) (m : Nat),
     args = [.ref r, .ref d, .ref wA, .ref aD] ∧ σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧
     Fields.get fsR arKey = some (.ref lAR) ∧
     σ.heap d = some (.plain "Cbtrn02c$DalytranRecord" fsd) ∧
     Fields.get fsd dAmtKey' = some (.long amt) ∧
     σ.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA) ∧ AllSome acKeys fsA ∧
     Fields.get fsA acBalKey = some (.long bal) ∧ Fields.get fsA acCcKey = some (.long cc) ∧
     Fields.get fsA acCdKey = some (.long cdb) ∧ Fields.get fsA acctIdKey = some (.long id) ∧
     σ.heap aD = some (.array (.cls "Cbtrn02c$AccountRecord") xsA) ∧ xsA.length < 2147483648 ∧
     AcctShapes σ xsA ∧ (∀ v ∈ xsA, v ≠ .ref wA) ∧
     0 ≤ firstIdx (fun v => longFieldOf σ acctIdKey v == some id) xsA ∧
     σ.heap lAR = some (.list .arrayList ys m) ∧ aD ≠ wA ∧ lAR ≠ wA ∧ r ≠ wA ∧ d ≠ wA ∧
     lAR ≠ aD ∧ σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$AccountRecord" = .done)
  (fun args σ r' σ' => ∀ (r d wA aD : Addr), args = [.ref r, .ref d, .ref wA, .ref aD] →
     ∃ (y1 y2 : Addr) (fs1 fs2 : List (FieldKey × Value)) (m' : Nat),
       σ'.heap wA = some (.plain "Cbtrn02c$AccountRecord" (acctPostFs (fieldsOf σ wA)
         (lng' σ wA acBalKey) (lng' σ wA acCcKey) (lng' σ wA acCdKey) (lng' σ d dAmtKey'))) ∧
       σ'.heap aD = some (.array (.cls "Cbtrn02c$AccountRecord") ((arrOf σ aD).set
         (firstIdx (fun v => longFieldOf σ acctIdKey v == some (lng' σ wA acctIdKey)) (arrOf σ aD)).toNat
         (.ref y1))) ∧
       σ'.heap y1 = some (.plain "Cbtrn02c$AccountRecord" fs1) ∧
       SameFields acKeys fs1 (acctPostFs (fieldsOf σ wA) (lng' σ wA acBalKey) (lng' σ wA acCcKey)
         (lng' σ wA acCdKey) (lng' σ d dAmtKey')) ∧
       σ'.heap (refField σ r arKey) =
         some (.list .arrayList (listOf σ (refField σ r arKey) ++ [.ref y2]) m') ∧
       σ'.heap y2 = some (.plain "Cbtrn02c$AccountRecord" fs2) ∧
       SameFields acKeys fs2 (acctPostFs (fieldsOf σ wA) (lng' σ wA acBalKey) (lng' σ wA acCcKey)
         (lng' σ wA acCdKey) (lng' σ d dAmtKey')) ∧
       σ.next ≤ y1 ∧ σ.next ≤ y2 ∧ y1 ≠ y2 ∧ FrameS σ σ' [wA, aD, refField σ r arKey] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

end EquivLean.Modernize.Cbtrn02c.Java
