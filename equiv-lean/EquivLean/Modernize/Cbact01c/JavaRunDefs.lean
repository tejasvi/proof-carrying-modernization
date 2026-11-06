import EquivLean.Modernize.Cbact01c.JavaRunZoned

/-!
# CBACT01C → Java: the account record object, the helper contracts, the `Result` lists

`AcctOk σ c`: the record object at `c` holds strings in its string fields and `long`s below
`10 ^ 18` in absolute value in its numeric fields (as every record of a valid file does).
`sfJ` / `zfJ`: the text of a string field, the `zoned` text of a `long` field.
`acctTextJ`: the text `accountRecordText` builds, against the contracts of `zoned` and `pad`.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

def acctCls : ClassName := "Cbact01c$AccountRecord"

/-- Field `f` of the record object at `c` (`null` if absent). -/
def fieldOf (σ : Jimple.State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (acctCls, f)).getD .null
  | _ => .null

/-- A `long` field of the record object at `c`. -/
def fieldLong (σ : Jimple.State) (c : Addr) (f : String) : I64 :=
  match fieldOf σ c f with
  | .long x => x
  | _ => 0

/-- The text of string field `f`. -/
def sfJ (σ : Jimple.State) (c : Addr) (f : String) : JStr := argText σ (fieldOf σ c f)

/-- The `zoned` text of `long` field `f`, in `n` digits. -/
def zfJ (σ : Jimple.State) (c : Addr) (f : String) (n : Nat) (signed : Bool) : JStr :=
  zonedJ (fieldLong σ c f).toInt n signed

/-- String field `f` holds a string. -/
def StrField (σ : Jimple.State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (acctCls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧
    s.length < 2147483648

/-- `long` field `f` holds a value below `10 ^ 18` in absolute value. -/
def LongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (acctCls, f) = some (.long a) ∧ a.toInt.natAbs < 10 ^ 18

/-- The record object at `c`, as the helpers read it. -/
def AcctOk (σ : Jimple.State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain acctCls fs) ∧ LongField fs "acctId" ∧
    StrField σ fs "acctActiveStatus" ∧ LongField fs "acctCurrBal" ∧
    LongField fs "acctCreditLimit" ∧ LongField fs "acctCashCreditLimit" ∧
    StrField σ fs "acctOpenDate" ∧ StrField σ fs "acctExpiraionDate" ∧
    StrField σ fs "acctReissueDate" ∧ LongField fs "acctCurrCycCredit" ∧
    LongField fs "acctCurrCycDebit" ∧ StrField σ fs "acctAddrZip" ∧ StrField σ fs "acctGroupId" ∧
    StrField σ fs "filler1"

/-- String field `f` holds a string object below `B`. -/
def StrFieldB (σ : Jimple.State) (fs : List (FieldKey × Value)) (f : String) (B : Addr) : Prop :=
  ∃ x s, Fields.get fs (acctCls, f) = some (.ref x) ∧ x < B ∧ σ.heap x = some (.str s) ∧
    s.length < 2147483648

/-- `AcctOk` with the record object and its strings below `B` (older than the objects at `B` and
above, as the input records are older than the `Result` lists). -/
def AcctOkB (σ : Jimple.State) (c : Addr) (B : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain acctCls fs) ∧ c < B ∧ LongField fs "acctId" ∧
    StrFieldB σ fs "acctActiveStatus" B ∧ LongField fs "acctCurrBal" ∧
    LongField fs "acctCreditLimit" ∧ LongField fs "acctCashCreditLimit" ∧
    StrFieldB σ fs "acctOpenDate" B ∧ StrFieldB σ fs "acctExpiraionDate" B ∧
    StrFieldB σ fs "acctReissueDate" B ∧ LongField fs "acctCurrCycCredit" ∧
    LongField fs "acctCurrCycDebit" ∧ StrFieldB σ fs "acctAddrZip" B ∧
    StrFieldB σ fs "acctGroupId" B ∧ StrFieldB σ fs "filler1" B

/-- The text `accountRecordText` builds for the record at `c`. -/
def acctTextJ (σ : Jimple.State) (c : Addr) : JStr :=
  zfJ σ c "acctId" 11 false ++ fixStr (sfJ σ c "acctActiveStatus") 1 ++
  zfJ σ c "acctCurrBal" 12 true ++ zfJ σ c "acctCreditLimit" 12 true ++
  zfJ σ c "acctCashCreditLimit" 12 true ++ fixStr (sfJ σ c "acctOpenDate") 10 ++
  fixStr (sfJ σ c "acctExpiraionDate") 10 ++ fixStr (sfJ σ c "acctReissueDate") 10 ++
  zfJ σ c "acctCurrCycCredit" 12 true ++ zfJ σ c "acctCurrCycDebit" 12 true ++
  fixStr (sfJ σ c "acctAddrZip") 10 ++ fixStr (sfJ σ c "acctGroupId") 10 ++
  fixStr (sfJ σ c "filler1") 178

def resCls : ClassName := "Cbact01c$Result"

/-- The elements of the list object at `l`. -/
def lElems (σ : Jimple.State) (l : Addr) : List Value :=
  match σ.heap l with
  | some (.list _ ys _) => ys
  | _ => []

/-- The modification count of the list object at `l`. -/
def lMods (σ : Jimple.State) (l : Addr) : Nat :=
  match σ.heap l with
  | some (.list _ _ m) => m
  | _ => 0

/-! ## The texts and objects the record methods build -/

/-- The lines `displayAcctRecord` adds for the record at `c`. -/
def dispLinesJ (σ : Jimple.State) (c : Addr) : List JStr :=
  [JStr.ofString "ACCT-ID                 :" ++ zfJ σ c "acctId" 11 false,
   JStr.ofString "ACCT-ACTIVE-STATUS      :" ++ sfJ σ c "acctActiveStatus",
   JStr.ofString "ACCT-CURR-BAL           :" ++ zfJ σ c "acctCurrBal" 12 true,
   JStr.ofString "ACCT-CREDIT-LIMIT       :" ++ zfJ σ c "acctCreditLimit" 12 true,
   JStr.ofString "ACCT-CASH-CREDIT-LIMIT  :" ++ zfJ σ c "acctCashCreditLimit" 12 true,
   JStr.ofString "ACCT-OPEN-DATE          :" ++ sfJ σ c "acctOpenDate",
   JStr.ofString "ACCT-EXPIRAION-DATE     :" ++ sfJ σ c "acctExpiraionDate",
   JStr.ofString "ACCT-REISSUE-DATE       :" ++ sfJ σ c "acctReissueDate",
   JStr.ofString "ACCT-CURR-CYC-CREDIT    :" ++ zfJ σ c "acctCurrCycCredit" 12 true,
   JStr.ofString "ACCT-CURR-CYC-DEBIT     :" ++ zfJ σ c "acctCurrCycDebit" 12 true,
   JStr.ofString "ACCT-GROUP-ID           :" ++ sfJ σ c "acctGroupId",
   JStr.ofString "-------------------------------------------------"]

/-- Line `i` of `dispLinesJ`. -/
def dispLine (σ : Jimple.State) (c : Addr) (i : Nat) : JStr := (dispLinesJ σ c).getD i []

/-- VBRC-REC1: the id, the status. -/
def vb1J (σ : Jimple.State) (c : Addr) : JStr :=
  zfJ σ c "acctId" 11 false ++ fixStr (sfJ σ c "acctActiveStatus") 1

/-- VBRC-REC2: the id, the balance, the credit limit, the first four characters of the reissue
date. -/
def vb2J (σ : Jimple.State) (c : Addr) : JStr :=
  zfJ σ c "acctId" 11 false ++ zfJ σ c "acctCurrBal" 12 true ++ zfJ σ c "acctCreditLimit" 12 true ++
    (fixStr (sfJ σ c "acctReissueDate") 10).take 4

def outCls : ClassName := "Cbact01c$OutAcctRec"

/-- The `OutAcctRec` at `o` in `σ'`, built from the record at `c` of `σ`, the date text `dt` and
the cycle debit `cd`; its strings are new (`nb` and above). -/
def OutRecJ (σ' : Jimple.State) (o : Addr) (σ : Jimple.State) (c : Addr) (dt : JStr) (cd : I64)
    (nb : Addr) : Prop :=
  ∃ fs, σ'.heap o = some (.plain outCls fs) ∧
    Fields.get fs (outCls, "outAcctId") = some (.long (fieldLong σ c "acctId")) ∧
    (∃ x, Fields.get fs (outCls, "outAcctActiveStatus") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr (sfJ σ c "acctActiveStatus") 1))) ∧
    Fields.get fs (outCls, "outAcctCurrBal") = some (.long (fieldLong σ c "acctCurrBal")) ∧
    Fields.get fs (outCls, "outAcctCreditLimit") = some (.long (fieldLong σ c "acctCreditLimit")) ∧
    Fields.get fs (outCls, "outAcctCashCreditLimit") =
      some (.long (fieldLong σ c "acctCashCreditLimit")) ∧
    (∃ x, Fields.get fs (outCls, "outAcctOpenDate") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr (sfJ σ c "acctOpenDate") 10))) ∧
    (∃ x, Fields.get fs (outCls, "outAcctExpiraionDate") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr (sfJ σ c "acctExpiraionDate") 10))) ∧
    (∃ x, Fields.get fs (outCls, "outAcctReissueDate") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr dt 10))) ∧
    Fields.get fs (outCls, "outAcctCurrCycCredit") =
      some (.long (fieldLong σ c "acctCurrCycCredit")) ∧
    Fields.get fs (outCls, "outAcctCurrCycDebit") = some (.long cd) ∧
    (∃ x, Fields.get fs (outCls, "outAcctGroupId") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr (sfJ σ c "acctGroupId") 10)))

/-- The fields of a new `OutAcctRec` (default values). -/
def outFields0 : List (FieldKey × Value) :=
  (Gen.prog.instanceFields outCls).map fun (k, t) => (k, t.default)

def arrCls : ClassName := "Cbact01c$ArrArrayRec"

/-- The balances: the record's twice, `-1025.00`, then zeros. -/
def balArr (b : I64) : List Value :=
  [.long b, .long b, .long (BitVec.ofInt 64 (-102500)), .long 0#64, .long 0#64]

/-- The cycle debits. -/
def debArr : List Value :=
  [.long (BitVec.ofInt 64 100500), .long (BitVec.ofInt 64 152500),
   .long (BitVec.ofInt 64 (-250000)), .long 0#64, .long 0#64]

/-- The `ArrArrayRec` at `o` in `σ'`, built from the record at `c` of `σ`; its arrays and string
are new (`nb` and above). -/
def ArrRecJ (σ' : Jimple.State) (o : Addr) (σ : Jimple.State) (c : Addr) (nb : Addr) : Prop :=
  ∃ fs, σ'.heap o = some (.plain arrCls fs) ∧
    Fields.get fs (arrCls, "arrAcctId") = some (.long (fieldLong σ c "acctId")) ∧
    (∃ b et, Fields.get fs (arrCls, "arrAcctCurrBal") = some (.ref b) ∧ nb ≤ b ∧
      σ'.heap b = some (.array et (balArr (fieldLong σ c "acctCurrBal")))) ∧
    (∃ b et, Fields.get fs (arrCls, "arrAcctCurrCycDebit") = some (.ref b) ∧ nb ≤ b ∧
      σ'.heap b = some (.array et debArr)) ∧
    (∃ x, Fields.get fs (arrCls, "arrFiller") = some (.ref x) ∧ nb ≤ x ∧
      σ'.heap x = some (.str (fixStr [] 4)))

def zonedSig : MethodSig :=
  ⟨"Cbact01c", .cls "java.lang.String", "zoned", [.prim .long, .prim .int, .prim .boolean]⟩
def padSig : MethodSig :=
  ⟨"Cbact01c", .cls "java.lang.String", "pad", [.cls "java.lang.String", .prim .int]⟩
def spacesSig : MethodSig := ⟨"Cbact01c", .cls "java.lang.String", "spaces", [.prim .int]⟩

/-- The helper contracts. -/
def textCallees : Contracts := [(zonedSig, zonedSpec), (padSig, padSpec)]

abbrev accountRecordTextRef : MethodRef :=
  Gen.Cbact01c.«accountRecordText(Cbact01c$AccountRecord)».ref

def accountRecordTextSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ AcctOk σ c ∧ σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (acctTextJ σ c)) ∧ σ.next ≤ x ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

end EquivLean.Modernize.Cbact01c.Java
