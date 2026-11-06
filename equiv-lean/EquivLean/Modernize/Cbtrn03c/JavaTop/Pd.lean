import EquivLean.Modernize.Cbtrn03c.JavaTop.Callees

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, definitions

`processDetail(ws, tran, xrefFile, trantypeFile, trancatgFile)` is `Model.tranStep`.  Cuts at
the calls whose contracts have premises (`writeAccountTotals` 14, `findXref` 18,
`findTranType` 34, `findTranCat` 48, `writeTransactionReport` 66) and after them (15, 19, 35, 49);
the model state along the paths: `pdS0` (the record displayed), `pdS1` (the account totals on a
change of card, unless first), `pdS1c` (the card number set), `cardOk` (the card step's state).
The ghost values are parameters (`pdSpecG`); `pd_sat` quantifies them (`processDetailSpecM`).

Locals: `r0` (the `Ws` object) 1, `$l1` 4, `r2` (xrefFile) 5, `r4` (trancatgFile) 7, `$i0` 8,
`i4` 9, `$r6` 10, `$r8` 11, `r3` (trantypeFile) 12, `r1` (the record) 13.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

abbrev pdRef : MethodRef :=
  Gen.Cbtrn03c.«processDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,Cbtrn03c$CardXrefRecord[],Cbtrn03c$TranTypeRecord[],Cbtrn03c$TranCatRecord[])».ref

abbrev Recs := List (List EquivLean.Cobol.Rec.FVal)
abbrev Rec := List EquivLean.Cobol.Rec.FVal

/-! ## The model along the paths -/

def pdS0 (s : Model.St) (t : Rec) : Model.St := Model.dsp s (Model.TranRecord.textS t)
def pdS1 (s : Model.St) (t : Rec) : Model.St :=
  if (pdS0 s t).first then pdS0 s t else Model.acctTotals (pdS0 s t)
def pdS1c (s : Model.St) (t : Rec) : Model.St := { pdS1 s t with card := Model.tCard t }
def cardOk (xs : Recs) (s : Model.St) (t : Rec) : Model.St := stOf (Model.cardStep xs (pdS0 s t) t)
def tyOf (ys : Recs) (t : Rec) : Rec := (ys.find? fun y => Model.yType y == Model.tType t).getD default
def caOf (cs : Recs) (t : Rec) : Rec :=
  (cs.find? fun c => Model.cType c == Model.tType t && Model.cCat c == Model.tCat t).getD default

def pdCallees : Contracts :=
  [(tranRecordTextSig, tranRecordTextSpecT), (writeAccountTotalsSig, writeAccountTotalsSpecM),
   (findXrefSig, findXrefSpecT), (ioStatusLineSig, ioStatusLineSpecT),
   (findTranTypeSig, findTranTypeSpecT), (findTranCatSig, findTranCatSpecT),
   (digitsSig, digitsSpecT), (writeTransactionReportSig, writeTransactionReportSpecM)]

/-- `processDetail` for given ghost values. -/
def pdSpecG (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs) : Spec :=
  Spec.of
  (fun args σ => args = [.ref w, .ref c, .ref a2, .ref a3, .ref a4] ∧
     WsRel σ w ld lr d s ∧ TranFields σ c t ∧ TranRecord.Valid t ∧ WsDateparmRecord.Valid d ∧
     XrefFileAt σ a2 xs ∧ TrantypeFileAt σ a3 ys ∧ TrancatgFileAt σ a4 cs ∧
     (∀ v ∈ xs, CardXrefRecord.Valid v) ∧ (∀ v ∈ ys, TranTypeRecord.Valid v) ∧
     (∀ v ∈ cs, TranCatRecord.Valid v) ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun _ σ r σ' =>
     r = some (.int (if okB (Model.tranStep xs ys cs d s t) then 0 else 1)) ∧
     WsRel σ' w ld lr d (stOf (Model.tranStep xs ys cs d s t)) ∧ KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The facts every cut keeps: the arguments in their locals, the record and the files, the
frame from the entry. -/
def PdC (w c a2 a3 a4 : Addr) (t : Rec) (xs ys cs : Recs) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  fr.get 1 = some (.ref w) ∧ fr.get 13 = some (.ref c) ∧ fr.get 5 = some (.ref a2) ∧
  fr.get 12 = some (.ref a3) ∧ fr.get 7 = some (.ref a4) ∧
  TranFields σ c t ∧ XrefFileAt σ a2 xs ∧ TrantypeFileAt σ a3 ys ∧ TrancatgFileAt σ a4 cs ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def pdInv (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs) : Invariants :=
  [(14, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧ WsRel σ w ld lr d (pdS0 s t) ∧
      (pdS0 s t).card ≠ Model.tCard t ∧ (pdS0 s t).first = false),
   (15, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧ WsRel σ w ld lr d (pdS1 s t) ∧
      (pdS0 s t).card ≠ Model.tCard t),
   (18, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧ WsRel σ w ld lr d (pdS1c s t) ∧
      (pdS0 s t).card ≠ Model.tCard t ∧
      ∃ y, fr.get 10 = some (.ref y) ∧ σ.heap y = some (.str (cp037Str (Model.tCard t)))),
   (19, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧ WsRel σ w ld lr d (pdS1c s t) ∧
      (pdS0 s t).card ≠ Model.tCard t ∧
      fr.get 8 = some (.int (BitVec.ofInt 32 (xrefIdx xs (Model.tCard t))))),
   (34, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧
      WsRel σ w ld lr d (cardOk xs s t) ∧
      Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t) ∧
      ∃ y, fr.get 10 = some (.ref y) ∧ σ.heap y = some (.str (cp037Str (Model.tType t)))),
   (35, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧
      WsRel σ w ld lr d (cardOk xs s t) ∧
      Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t) ∧
      fr.get 8 = some (.int (BitVec.ofInt 32 (typeIdx ys (Model.tType t))))),
   (48, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧
      WsRel σ w ld lr d (cardOk xs s t) ∧
      Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t) ∧ 0 ≤ typeIdx ys (Model.tType t) ∧
      fr.get 8 = some (.int (BitVec.ofInt 32 (typeIdx ys (Model.tType t)))) ∧
      fr.get 4 = some (.long (BitVec.ofInt 64 (Model.tCat t))) ∧
      ∃ y, fr.get 10 = some (.ref y) ∧ σ.heap y = some (.str (cp037Str (Model.tType t)))),
   (49, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧
      WsRel σ w ld lr d (cardOk xs s t) ∧
      Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t) ∧ 0 ≤ typeIdx ys (Model.tType t) ∧
      fr.get 8 = some (.int (BitVec.ofInt 32 (typeIdx ys (Model.tType t)))) ∧
      fr.get 9 = some (.int (BitVec.ofInt 32 (catIdx cs (Model.tType t) (Model.tCat t))))),
   (66, fun _ σ0 fr σ => PdC w c a2 a3 a4 t xs ys cs σ0 fr σ ∧
      WsRel σ w ld lr d (cardOk xs s t) ∧
      Model.tranStep xs ys cs d s t = .ok (Model.report d (cardOk xs s t) t (tyOf ys t) (caOf cs t)) ∧
      TranTypeRecord.Valid (tyOf ys t) ∧ TranCatRecord.Valid (caOf cs t) ∧
      ∃ ty ca, fr.get 10 = some (.ref ty) ∧ fr.get 11 = some (.ref ca) ∧
        σ.heap ty = some (.str (cp037Str (Model.yDesc (tyOf ys t)))) ∧
        σ.heap ca = some (.str (cp037Str (Model.cDesc (caOf cs t)))))]

/-- The paths of `processDetail` from statement `pc`. -/
def pdWP (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog pdCallees.env 0)
    Gen.Cbtrn03c.«processDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,Cbtrn03c$CardXrefRecord[],Cbtrn03c$TranTypeRecord[],Cbtrn03c$TranCatRecord[])»
    ((pdInv w ld lr c a2 a3 a4 d t s xs ys cs).inst args σ0)
    ((pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs).post args σ0) 120 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java.Top
