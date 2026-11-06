import EquivLean.Modernize.Cbtrn01c.JavaRunFields
import EquivLean.Modernize.Cbtrn01c.JavaRunModel

/-!
# CBTRN01C → Java: definitions for the proof of `run`

The contract `runSpecG` fixes the ghost values (the input arrays and the field values of the
transaction, cross-reference and account records) as parameters; `runSpec` of `JavaProof.lean`
follows in `JavaRun.lean`.

Cut points of `run`'s body (statement indices of the imported Jimple):
* 22 — before the constructor of the record area (`J22`): after the eleven `spaces` calls;
* 29 — the head of the read loop (`J29`): the lines of `headL` after `k` reads;
* 60 — the head of the cross-reference search (`J60`): the lines of `befL`, no match in the first
  `i` cross-reference records;
* 92 — the head of the account search (`J92`): the cross-reference record `x` was found, no match
  in the first `j` account records.

Locals: 10 `dalytranFile`, 35 `xrefFile`, 4 `accountFile`, 9 the `Result`, 11 its `displays`,
17 `dalPos`, 7 `dalEofHit`, 8 `endOfFile`, 5 the loop condition, 1 `dal`, 16 / 18 the search
indices, 20 the card number, 34 / 32 the found records, 12 `wsXrefReadStatus`, 13 `xrefAcctId`,
14 `xrefCustId` then `wsAcctReadStatus`, 15 `acctId`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-! ## Callees -/

def spacesSig : MethodSig := ⟨"Cbtrn01c", .cls "java.lang.String", "spaces", [.prim .int]⟩
def formatDalytranSig : MethodSig :=
  ⟨"Cbtrn01c", .cls "java.lang.String", "formatDalytran", [.cls "Cbtrn01c$DalytranRecord"]⟩

/-- The callee contracts of `run`. -/
def callees : Contracts :=
  [(spacesSig, spacesSpec), (digitsSig, digitsSpec), (formatDalytranSig, formatDalytranSpec)]

abbrev runBody := Gen.Cbtrn01c.«run(Cbtrn01c$DalytranRecord[],Cbtrn01c$FdCustfileRec[],Cbtrn01c$CardXrefRecord[],Cbtrn01c$FdCardfileRec[],Cbtrn01c$AccountRecord[],Cbtrn01c$FdTranfileRec[])»

/-! ## Objects -/

/-- The record object in `dal`: the strings of its card number and of its id. -/
def CurAt (σ : State) (d : Value) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ x fs c i, d = .ref x ∧ σ.heap x = some (.plain dalCls fs) ∧
    Fields.get fs (dalCls, "dalytranCardNum") = some (.ref c) ∧
    σ.heap c = some (.str (cp037Str (Model.strOf (t.getD 10 default)))) ∧
    Fields.get fs (dalCls, "dalytranId") = some (.ref i) ∧
    σ.heap i = some (.str (cp037Str (Model.strOf (t.getD 0 default))))

/-- The `Result` object: its `displays` list and `abended = false`. -/
def ResAt (σ : State) (res l : Addr) : Prop :=
  ∃ fs, σ.heap res = some (.plain "Cbtrn01c$Result" fs) ∧
    Fields.get fs ("Cbtrn01c$Result", "displays") = some (.ref l) ∧
    Fields.get fs ("Cbtrn01c$Result", "abended") = some (.int 0)

/-- The `displays` list holds the lines `D`. -/
def ListAt (σ : State) (l : Addr) (D : List (List Nat)) : Prop :=
  ∃ ys m, σ.heap l = some (.list .arrayList ys m) ∧ Hide (Forall2 (JStrAt σ) ys (D.map jline))

/-! ## The contract with fixed ghost values -/

/-- The inputs: the three files read, as arrays of record objects with valid field values. -/
def Inputs (a1 a3 a5 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (σ : State) : Prop :=
  DalytranFileAt σ a1 vals1 ∧ XrefFileAt σ a3 vals3 ∧ AccountFileAt σ a5 vals5 ∧
  (∀ v ∈ vals1, DalytranRecord.Valid v) ∧ (∀ v ∈ vals3, CardXrefRecord.Valid v) ∧
  (∀ v ∈ vals5, AccountRecord.Valid v)

/-- The classes are initialized. -/
def Inits (σ : State) : Prop :=
  σ.initOf "Cbtrn01c" = .done ∧ σ.initOf "Cbtrn01c$Result" = .done ∧
  σ.initOf "Cbtrn01c$AccountRecord" = .done ∧ σ.initOf "Cbtrn01c$CardXrefRecord" = .done ∧
  σ.initOf "Cbtrn01c$DalytranRecord" = .done ∧ σ.initOf "Cbtrn01c$FdCardfileRec" = .done ∧
  σ.initOf "Cbtrn01c$FdCustfileRec" = .done ∧ σ.initOf "Cbtrn01c$FdTranfileRec" = .done

def runArgs (a1 a2 a3 a4 a5 a6 : Addr) : List Value :=
  [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5, .ref a6]

def runPreG (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (args : List Value) (σ : State) : Prop :=
  args = runArgs a1 a2 a3 a4 a5 a6 ∧ Inputs a1 a3 a5 vals1 vals3 vals5 σ ∧ Inits σ

def runPostG (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods, r = some (.ref res) ∧
    σ'.heap res = some (.plain "Cbtrn01c$Result" fs) ∧
    Fields.get fs ("Cbtrn01c$Result", "displays") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧
    Forall2 (JStrAt σ') xs ((Model.displayText vals1 vals3 vals5).map jline) ∧
    Fields.get fs ("Cbtrn01c$Result", "abended") = some (.int 0)

def runSpecG (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) : Spec :=
  Spec.of (runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5)
    (fun _ _ r σ' => runPostG vals1 vals3 vals5 r σ')

/-! ## Invariants -/

/-- Facts at every cut point: the locals of the arrays, the `Result` and its list, `dalPos = k`,
the three end-of-file flags `= e`, the record object `d` in `dal` (the record area after `k`
reads), the heap grown from the entry state, `Cbtrn01c` initialized. -/
def Base (a1 a3 a5 : Addr) (vals1 : List (List EquivLean.Cobol.Rec.FVal)) (σ0 : State) (fr : Frame) (σ : State)
    (k : Nat) (e : Bool) (d : Value) (res l : Addr) : Prop :=
  fr.get 10 = some (.ref a1) ∧ fr.get 35 = some (.ref a3) ∧ fr.get 4 = some (.ref a5) ∧
  fr.get 9 = some (.ref res) ∧ fr.get 11 = some (.ref l) ∧
  fr.get 17 = some (.int (BitVec.ofNat 32 k)) ∧ k ≤ vals1.length ∧
  fr.get 7 = some (.int (JInt.ofBool e)) ∧ fr.get 8 = some (.int (JInt.ofBool e)) ∧
  fr.get 5 = some (.int (JInt.ofBool e)) ∧ (e = true → k = vals1.length) ∧
  fr.get 1 = some d ∧ Hide (CurAt σ d (curT vals1 k)) ∧
  ResAt σ res l ∧ σ0.next ≤ res ∧ σ0.next ≤ l ∧ res ≠ l ∧ Grows σ0 σ ∧
  σ.initOf "Cbtrn01c" = .done

/-- The fields of a new `Cbtrn01c$DalytranRecord` (`null` and `0L`). -/
def dalFields0 : List (FieldKey × Value) :=
  [(("Cbtrn01c$DalytranRecord", "dalytranId"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranTypeCd"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranCatCd"), .long 0#64),
   (("Cbtrn01c$DalytranRecord", "dalytranSource"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranDesc"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranAmt"), .long 0#64),
   (("Cbtrn01c$DalytranRecord", "dalytranMerchantId"), .long 0#64),
   (("Cbtrn01c$DalytranRecord", "dalytranMerchantName"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranMerchantCity"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranMerchantZip"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranCardNum"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranOrigTs"), .null),
   (("Cbtrn01c$DalytranRecord", "dalytranProcTs"), .null),
   (("Cbtrn01c$DalytranRecord", "filler1"), .null)]

/-- The fields of the record area after its constructor (the strings `s20` … `s30`, zeros). -/
def dalFieldsAt (s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 : Addr) : List (FieldKey × Value) :=
  Fields.set (Fields.set (Fields.set (Fields.set (Fields.set (Fields.set (Fields.set (Fields.set
    (Fields.set (Fields.set (Fields.set (Fields.set (Fields.set (Fields.set dalFields0
    ("Cbtrn01c$DalytranRecord", "dalytranId") (.ref s20))
    ("Cbtrn01c$DalytranRecord", "dalytranTypeCd") (.ref s21))
    ("Cbtrn01c$DalytranRecord", "dalytranCatCd") (.long 0#64))
    ("Cbtrn01c$DalytranRecord", "dalytranSource") (.ref s22))
    ("Cbtrn01c$DalytranRecord", "dalytranDesc") (.ref s23))
    ("Cbtrn01c$DalytranRecord", "dalytranAmt") (.long 0#64))
    ("Cbtrn01c$DalytranRecord", "dalytranMerchantId") (.long 0#64))
    ("Cbtrn01c$DalytranRecord", "dalytranMerchantName") (.ref s24))
    ("Cbtrn01c$DalytranRecord", "dalytranMerchantCity") (.ref s25))
    ("Cbtrn01c$DalytranRecord", "dalytranMerchantZip") (.ref s26))
    ("Cbtrn01c$DalytranRecord", "dalytranCardNum") (.ref s27))
    ("Cbtrn01c$DalytranRecord", "dalytranOrigTs") (.ref s28))
    ("Cbtrn01c$DalytranRecord", "dalytranProcTs") (.ref s29))
    ("Cbtrn01c$DalytranRecord", "filler1") (.ref s30)

/-- Local `j` holds a string of `n` spaces. -/
def SpAt (σ : State) (fr : Frame) (j n : Nat) : Prop :=
  ∃ s, fr.get j = some (.ref s) ∧ σ.heap s = some (.str (spJ n))

/-- Before the constructor of the record area (statement 22): the `Result` with the start line,
the new record object, the eleven strings of spaces for its fields. -/
def J22 (a1 a3 a5 : Addr) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (r8 res l : Addr),
    fr.get 10 = some (.ref a1) ∧ fr.get 35 = some (.ref a3) ∧ fr.get 4 = some (.ref a5) ∧
    fr.get 9 = some (.ref res) ∧ fr.get 11 = some (.ref l) ∧ fr.get 1 = some (.ref r8) ∧
    σ.heap r8 = some (.plain dalCls dalFields0) ∧
    SpAt σ fr 20 16 ∧ SpAt σ fr 21 2 ∧ SpAt σ fr 22 10 ∧ SpAt σ fr 23 100 ∧ SpAt σ fr 24 50 ∧
    SpAt σ fr 25 50 ∧ SpAt σ fr 26 10 ∧ SpAt σ fr 27 16 ∧ SpAt σ fr 28 26 ∧ SpAt σ fr 29 26 ∧
    SpAt σ fr 30 20 ∧ ResAt σ res l ∧ ListAt σ l [startL] ∧
    σ0.next ≤ res ∧ σ0.next ≤ l ∧ σ0.next ≤ r8 ∧ res ≠ l ∧ Grows σ0 σ ∧
    σ.initOf "Cbtrn01c" = .done

/-- The head of the read loop (statement 29). -/
def J29 (a1 a3 a5 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (k : Nat) (e : Bool) (d : Value) (res l : Addr), Base a1 a3 a5 vals1 σ0 fr σ k e d res l ∧
    ListAt σ l (headL vals1 vals3 vals5 k e)

/-- No cross-reference record among the first `i` has the card number of `t`. -/
def NoCard (xs : List (List EquivLean.Cobol.Rec.FVal)) (i : Nat) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∀ x ∈ xs.take i, cardMatch t x = false

/-- No account record among the first `j` has the account id of `x`. -/
def NoAcct (accs : List (List EquivLean.Cobol.Rec.FVal)) (j : Nat) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∀ a ∈ accs.take j, acctMatch x a = false

/-- The head of the cross-reference search (statement 60). -/
def J60 (a1 a3 a5 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (k : Nat) (e : Bool) (d : Value) (res l : Addr) (i : Nat) (cs : Addr), Base a1 a3 a5 vals1 σ0 fr σ k e d res l ∧
    (e = false → 1 ≤ k) ∧ ListAt σ l (befL vals1 vals3 vals5 k e) ∧
    fr.get 16 = some (.int (BitVec.ofNat 32 i)) ∧ i ≤ vals3.length ∧
    fr.get 20 = some (.ref cs) ∧
    σ.heap cs = some (.str (cp037Str (Model.strOf ((curT vals1 k).getD 10 default)))) ∧
    fr.get 34 = some .null ∧ fr.get 12 = some (.long 0) ∧ NoCard vals3 i (curT vals1 k)

/-- The head of the account search (statement 92): `x` is the cross-reference record found. -/
def J92 (a1 a3 a5 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (k : Nat) (e : Bool) (d : Value) (res l : Addr) (j : Nat) (x : List EquivLean.Cobol.Rec.FVal), Base a1 a3 a5 vals1 σ0 fr σ k e d res l ∧
    (e = false → 1 ≤ k) ∧ vals3.find? (cardMatch (curT vals1 k)) = some x ∧
    ListAt σ l (befL vals1 vals3 vals5 k e ++ xrefL x) ∧
    fr.get 18 = some (.int (BitVec.ofNat 32 j)) ∧ j ≤ vals5.length ∧
    fr.get 13 = some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 2 default)))) ∧
    fr.get 15 = some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 2 default)))) ∧
    fr.get 14 = some (.long 0) ∧ fr.get 32 = some .null ∧ NoAcct vals5 j x

def runInv (a1 a3 a5 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) : Invariants :=
  [(22, J22 a1 a3 a5), (29, J29 a1 a3 a5 vals1 vals3 vals5), (60, J60 a1 a3 a5 vals1 vals3 vals5),
   (92, J92 a1 a3 a5 vals1 vals3 vals5)]

/-- Symbolic execution of `run`'s body from `pc` (callees by their contracts, constructors
inlined). -/
def RunWP (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (σ0 : State)
    (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog callees.env 1) runBody
    ((runInv a1 a3 a5 vals1 vals3 vals5).inst (runArgs a1 a2 a3 a4 a5 a6) σ0)
    ((runSpecG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5).post (runArgs a1 a2 a3 a4 a5 a6) σ0)
    60 pc fr σ

/- `RunWP` is unfolded explicitly (`unfold RunWP`): `whnf` must not run the symbolic execution
when a verification condition is applied. -/
attribute [irreducible] RunWP

end EquivLean.Modernize.Cbtrn01c.Java
