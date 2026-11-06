import EquivLean.Modernize.Cbtrn03c.JavaSpec

/-!
# CBTRN03C → Java: the interface between the top layer and the working-state writers

Shared by the Java maintainer session (top layer: `run`'s loop, `processDetail`, `processEnd`, the step to `runSpec`) and
cir-repin (bottom layer: the writers of the working state).  Everything here is a definition or a
contract statement; no proofs.

* `WsRel σ w ld lr d s`: the `Ws` object at `w` holds the model state `s` (`Model.St`), for the
  date parameter record `d`: its scalar fields are `s`'s counters, totals, first-time flag and
  the account id of `s.xref`; its display list (at `ld`, shared with the `Result` object) holds
  strings with the texts `s.disp.map jline`; its report list (at `lr`) holds `FdReptfileRec`
  objects with the texts `s.writes.map recLine`; its card and
  date strings hold the CP037 texts of `s.card`, `dStart d`, `dEnd d`.  The model sets
  `rs`/`re` at the first report line, the Java at the start: they agree once `first` is false.
* `KeepsNonWs σ σ'`: what a working-state helper keeps (every string, array and plain object of
  a class other than `Ws`); the caller's records and the `Result` object stay.
* `TranFields σ c t`: the `TranRecord` object at `c` holds the field values `t`.
* The writers' contracts on the model (`write…SpecM`), to be proved by cir-repin as
  `writeAccountTotalsM_ok`, `writePageTotalsM_ok`, `writeGrandTotalsM_ok`,
  `writeTransactionReportM_ok : ContractOK Gen.prog …Sig …SpecM`.
* The top layer's contracts (`processDetailSpecM`, `processEndSpecM`), proved by the Java maintainer session.

Contract style: the precondition takes the ghost values (`ld`, `lr`, `d`, `s`, `t`, …)
existentially; the postcondition quantifies them again with the precondition's facts as
premises (only the argument equations and the facts that pin the ghost values), and states the
result as a model function of them.  The callers (the Java maintainer session's segments) call each of these at a cut
point of their own, so the premises are hypotheses of the call's state.  To prove such a
contract, fix the ghosts: prove `MethodVC` for the contract with the ghosts as parameters (pre
`args = [.ref w] ∧ WsRel σ w ld lr d s ∧ …`, post the conclusion), then combine (given the
combined precondition and a postcondition's ghosts, apply the fixed contract's `Sat` at those
ghosts; `the Java maintainer session`'s `T3X/PeVC.lean` does this for `processEnd`).  `WsRel`, `KeepsNonWs`,
`TranFields` unfold to `∃`/`∧`: `jvc` destructures them in hypotheses unless they are
`attribute [local irreducible]` (as the Java maintainer session's call segments keep them).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

def wsC : ClassName := "Cbtrn03c$Ws"
def fdC : ClassName := "Cbtrn03c$FdReptfileRec"
def resC : ClassName := "Cbtrn03c$Result"
def tranC : ClassName := "Cbtrn03c$TranRecord"

/-! ## Report records -/

/-- The text of the report record `v` (field `fdReptfileRec` of an `FdReptfileRec` object). -/
def recText (σ : State) (v : Value) : Option JStr :=
  match v with
  | .ref x => match σ.heap x with
    | some (.plain c fs) =>
      if c = fdC then (match Fields.get fs (fdC, "fdReptfileRec") with
        | some s => strOf σ s
        | none => none)
      else none
    | _ => none
  | _ => none

/-- The values `ys` refer to report records holding the texts `ss`, in order. -/
def RecsAt (σ : State) (ys : List Value) (ss : List JStr) : Prop :=
  ys.map (recText σ) = ss.map some

/-- A written line as the report record's text: the CP037 text of the line's EBCDIC bytes (what
`runSpec`'s `JRecAt FdReptfileRec` asks of the record). -/
def recLine (l : List Nat) : JStr := cp037Str (l.map Model.ebc)

/-! ## The working state -/

/-- The model state's counters and totals are in range (`PIC 9(09)`, `S9(09)V99`), and the account
id of its cross-reference record (`PIC 9(11)`). -/
def StOk (s : Model.St) : Prop :=
  s.lc < 1000000000 ∧ s.page.natAbs < 100000000000 ∧ s.acct.natAbs < 100000000000 ∧
  s.grand.natAbs < 100000000000 ∧ (Model.xAcct s.xref).natAbs < 100000000000

/-- **The `Ws` object at `w` holds the model state `s`** (date parameters `d`). -/
def WsRel (σ : State) (w ld lr : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St) :
    Prop :=
  ∃ fs dsp wrs dm wm c rx ex, σ.heap w = some (.plain wsC fs) ∧
    Fields.get fs (wsC, "displays") = some (.ref ld) ∧
    Fields.get fs (wsC, "writes") = some (.ref lr) ∧
    Fields.get fs (wsC, "firstTime") = some (.int (if s.first then 1 else 0)) ∧
    Fields.get fs (wsC, "currCardNum") = some (.ref c) ∧
    Fields.get fs (wsC, "startDate") = some (.ref rx) ∧
    Fields.get fs (wsC, "endDate") = some (.ref ex) ∧
    Fields.get fs (wsC, "xrefAcctId") = some (.long (BitVec.ofInt 64 (Model.xAcct s.xref))) ∧
    Fields.get fs (wsC, "lineCounter") = some (.long (BitVec.ofNat 64 s.lc)) ∧
    Fields.get fs (wsC, "pageTotal") = some (.long (BitVec.ofInt 64 s.page)) ∧
    Fields.get fs (wsC, "accountTotal") = some (.long (BitVec.ofInt 64 s.acct)) ∧
    Fields.get fs (wsC, "grandTotal") = some (.long (BitVec.ofInt 64 s.grand)) ∧
    σ.heap ld = some (.list .arrayList dsp dm) ∧ σ.heap lr = some (.list .arrayList wrs wm) ∧
    w ≠ ld ∧ w ≠ lr ∧ ld ≠ lr ∧
    StrsAt σ dsp (s.disp.map jline) ∧ RecsAt σ wrs (s.writes.map recLine) ∧
    σ.heap c = some (.str (cp037Str s.card)) ∧
    σ.heap rx = some (.str (cp037Str (Model.dStart d))) ∧
    σ.heap ex = some (.str (cp037Str (Model.dEnd d))) ∧
    (s.first = false → s.rs = Model.cps (Model.dStart d) ∧ s.re = Model.cps (Model.dEnd d)) ∧
    StOk s

/-- What a working-state helper keeps: the heap grows; every string, every array and every
plain object of a class other than `Ws` stays (the lists it changes are the `Ws` object's). -/
def KeepsNonWs (σ σ' : State) : Prop :=
  σ.next ≤ σ'.next ∧ StrMono σ σ' ∧
  (∀ x c fs, σ.heap x = some (.plain c fs) → c ≠ wsC → σ'.heap x = some (.plain c fs)) ∧
  (∀ x et xs, σ.heap x = some (.array et xs) → σ'.heap x = some (.array et xs))

/-! ## Transaction records -/

/-- String field `f` (class `cls`, fields `fs`) holds the CP037 text of `bs`. -/
def SFld (σ : State) (cls : ClassName) (fs : List (FieldKey × Value)) (f : String)
    (bs : List UInt8) : Prop :=
  ∃ y, Fields.get fs (cls, f) = some (.ref y) ∧ σ.heap y = some (.str (cp037Str bs))

/-- `long` field `f` (class `cls`, fields `fs`) holds `v`. -/
def LFld (cls : ClassName) (fs : List (FieldKey × Value)) (f : String) (v : Int) : Prop :=
  Fields.get fs (cls, f) = some (.long (BitVec.ofInt 64 v))

/-- **The `TranRecord` object at `c` holds the field values `t`** (`JRecAt TranRecord` with the
fields spelled out, for a valid `t`; through the model's accessors where it has them). -/
def TranFields (σ : State) (c : Addr) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ fs, σ.heap c = some (.plain tranC fs) ∧
    SFld σ tranC fs "tranId" (Model.tId t) ∧
    SFld σ tranC fs "tranTypeCd" (Model.tType t) ∧
    LFld tranC fs "tranCatCd" (Model.tCat t) ∧
    SFld σ tranC fs "tranSource" (Model.tSource t) ∧
    SFld σ tranC fs "tranDesc" (Model.strOf (t.getD 4 default)) ∧
    LFld tranC fs "tranAmt" (Model.tAmt t) ∧
    LFld tranC fs "tranMerchantId" (Model.numOf (t.getD 6 default)) ∧
    SFld σ tranC fs "tranMerchantName" (Model.strOf (t.getD 7 default)) ∧
    SFld σ tranC fs "tranMerchantCity" (Model.strOf (t.getD 8 default)) ∧
    SFld σ tranC fs "tranMerchantZip" (Model.strOf (t.getD 9 default)) ∧
    SFld σ tranC fs "tranCardNum" (Model.tCard t) ∧
    SFld σ tranC fs "tranOrigTs" (Model.strOf (t.getD 11 default)) ∧
    SFld σ tranC fs "tranProcTs" (Model.strOf (t.getD 12 default)) ∧
    SFld σ tranC fs "filler1" (Model.strOf (t.getD 13 default))

/-! ## The model's result of a transaction -/

/-- The state of a step's result (the abend's state for `.error`). -/
def stOf : Except Model.St Model.St → Model.St
  | .ok s => s
  | .error s => s

/-- Whether a step went on (`processDetail` returns `false`). -/
def okB : Except Model.St Model.St → Bool
  | .ok _ => true
  | .error _ => false

/-! ## The writers' contracts on the model (cir-repin) -/

def writeAccountTotalsSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writeAccountTotals", [.cls "Cbtrn03c$Ws"]⟩
def writePageTotalsSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writePageTotals", [.cls "Cbtrn03c$Ws"]⟩
def writeGrandTotalsSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writeGrandTotals", [.cls "Cbtrn03c$Ws"]⟩
def writeTransactionReportSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writeTransactionReport",
    [.cls "Cbtrn03c$Ws", .cls "Cbtrn03c$TranRecord", .cls "java.lang.String", .cls "java.lang.String"]⟩

/-- A writer of the working state that performs the model step `f` (`writeAccountTotals`:
`Model.acctTotals`, `writePageTotals`: `Model.pageTotals`, `writeGrandTotals`:
`Model.grandTotals`). -/
def wsStepSpec (f : Model.St → Model.St) : Spec := Spec.of
  (fun args σ => ∃ w ld lr d s, args = [.ref w] ∧ WsRel σ w ld lr d s ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr d s, args = [.ref w] → WsRel σ w ld lr d s →
     r = none ∧ WsRel σ' w ld lr d (f s) ∧ KeepsNonWs σ σ' ∧ σ'.inits = σ.inits ∧
     σ'.statics = σ.statics)

def writeAccountTotalsSpecM : Spec := wsStepSpec Model.acctTotals
def writePageTotalsSpecM : Spec := wsStepSpec Model.pageTotals
def writeGrandTotalsSpecM : Spec := wsStepSpec Model.grandTotals

/-- `writeTransactionReport(ws, tran, typeDesc, catDesc)`: `Model.report d s t y cc` (the type
and category records `y`, `cc` enter through their descriptions). -/
def writeTransactionReportSpecM : Spec := Spec.of
  (fun args σ => ∃ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] ∧
     WsRel σ w ld lr d s ∧ TranFields σ c t ∧ TranRecord.Valid t ∧ WsDateparmRecord.Valid d ∧
     TranTypeRecord.Valid y ∧ TranCatRecord.Valid cc ∧
     σ.heap ty = some (.str (cp037Str (Model.yDesc y))) ∧
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] →
     WsRel σ w ld lr d s → TranFields σ c t → TranRecord.Valid t → WsDateparmRecord.Valid d →
     TranTypeRecord.Valid y → TranCatRecord.Valid cc →
     σ.heap ty = some (.str (cp037Str (Model.yDesc y))) →
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) →
     r = none ∧ WsRel σ' w ld lr d (Model.report d s t y cc) ∧ KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-! ## The top layer's contracts (the Java maintainer session) -/

def processDetailSig : MethodSig :=
  ⟨"Cbtrn03c", .prim .boolean, "processDetail",
    [.cls "Cbtrn03c$Ws", .cls "Cbtrn03c$TranRecord", .array (.cls "Cbtrn03c$CardXrefRecord"),
     .array (.cls "Cbtrn03c$TranTypeRecord"), .array (.cls "Cbtrn03c$TranCatRecord")]⟩
def processEndSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "processEnd", [.cls "Cbtrn03c$Ws", .cls "Cbtrn03c$TranRecord"]⟩

/-- `processDetail(ws, tran, xrefFile, trantypeFile, trancatgFile)`: `Model.tranStep`; returns
`true` (1) exactly on the abend. -/
def processDetailSpecM : Spec := Spec.of
  (fun args σ => ∃ w ld lr c a2 a3 a4 d s t xs ys cs,
     args = [.ref w, .ref c, .ref a2, .ref a3, .ref a4] ∧
     WsRel σ w ld lr d s ∧ TranFields σ c t ∧ TranRecord.Valid t ∧ WsDateparmRecord.Valid d ∧
     XrefFileAt σ a2 xs ∧ TrantypeFileAt σ a3 ys ∧ TrancatgFileAt σ a4 cs ∧
     (∀ v ∈ xs, CardXrefRecord.Valid v) ∧ (∀ v ∈ ys, TranTypeRecord.Valid v) ∧
     (∀ v ∈ cs, TranCatRecord.Valid v) ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr c a2 a3 a4 d s t xs ys cs,
     args = [.ref w, .ref c, .ref a2, .ref a3, .ref a4] →
     WsRel σ w ld lr d s → TranFields σ c t → TranRecord.Valid t → WsDateparmRecord.Valid d →
     XrefFileAt σ a2 xs → TrantypeFileAt σ a3 ys → TrancatgFileAt σ a4 cs →
     (∀ v ∈ xs, CardXrefRecord.Valid v) → (∀ v ∈ ys, TranTypeRecord.Valid v) →
     (∀ v ∈ cs, TranCatRecord.Valid v) →
     r = some (.int (if okB (Model.tranStep xs ys cs d s t) then 0 else 1)) ∧
     WsRel σ' w ld lr d (stOf (Model.tranStep xs ys cs d s t)) ∧ KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `processEnd(ws, tran)`: `Model.eofTail`. -/
def processEndSpecM : Spec := Spec.of
  (fun args σ => ∃ w ld lr c d s t, args = [.ref w, .ref c] ∧ WsRel σ w ld lr d s ∧
     TranFields σ c t ∧ TranRecord.Valid t ∧ σ.initOf "Cbtrn03c" = .done ∧
     σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr c d s t, args = [.ref w, .ref c] → WsRel σ w ld lr d s →
     TranFields σ c t → TranRecord.Valid t →
     r = none ∧ WsRel σ' w ld lr d (Model.eofTail s t) ∧ KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

end EquivLean.Modernize.Cbtrn03c.Java.Top
