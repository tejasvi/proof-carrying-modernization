import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMS
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWAb

/-!
# CBTRN02C → Java: the contract of `postTransaction`

`postTransaction` posts a valid daily transaction: it fills `tranWs` from the transaction and the
clock, updates the category balance (`updateTcatbal`), the account (`updateAccount`), and writes
the transaction (`writeTransaction`).  Its contract states the effect on the model state: `W` holds
`Model.St.post` after the call (ghost values: the addresses `A`, the model state `s`, the
transaction `t`, its cross-reference `x` and account `a`, the clock `clk`).

Cut points: 36 (before `updateTcatbal`), 39 (before `updateAccount`), 40 (before
`writeTransaction`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev dalCls : ClassName := "Cbtrn02c$DalytranRecord"

/-- The ghost values of a call of `postTransaction`. -/
structure PG where
  A : Addrs
  s : Model.St
  t : List EquivLean.Cobol.Rec.FVal
  x : List EquivLean.Cobol.Rec.FVal
  a : List EquivLean.Cobol.Rec.FVal
  clk : List UInt8
  d : Addr
  cs : Addr

/-- The arguments of the call. -/
def PG.args (p : PG) : List Value :=
  [.ref p.A.r, .ref p.d, .ref p.cs, .ref p.A.wX, .ref p.A.wA, .ref p.A.wC, .ref p.A.wT, .ref p.A.aD,
   .ref p.A.lC, .ref p.A.lK]

/-- The lists stay below the JVM bounds after one more element. -/
def PtLen (s : Model.St) : Prop :=
  s.cats.length < 2147483647 ∧ s.catW.length + 1 < 2147483648 ∧
  s.catRW.length + 1 < 2147483648 ∧ s.disp.length + 4 < 2147483648 ∧
  s.acctRW.length + 1 < 2147483648 ∧ s.tranW.length + 1 < 2147483648

/-- **What `postTransaction` needs**: `W` for the model state, the transaction record `d`, the
cross-reference and account in the work-storage records (as `validateTran` left them), the
clock, room in the lists, the classes initialized. -/
def PtFacts (σ : State) (p : PG) : Prop :=
  W σ p.A p.s ∧ MV p.s ∧
  JRecAt DalytranRecord dalCls σ (.ref p.d) p.t ∧ DalytranRecord.Valid p.t ∧
  JRecAt CardXrefRecord xrCls σ (.ref p.A.wX) p.x ∧ CardXrefRecord.Valid p.x ∧
  JRecAt AccountRecord acCls σ (.ref p.A.wA) p.a ∧
  Model.findAcct p.s.accts (Model.xAcct p.x) = some p.a ∧
  JStrAt σ (.ref p.cs) (cp037Str p.clk) ∧ CurrentDate p.clk ∧ PtLen p.s ∧ Inits σ ∧
  (∃ xs, σ.heap p.A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs))

/-- The objects `postTransaction` may change. -/
def PtMod (A : Addrs) : List Addr :=
  [A.wT, A.wC, A.lC, A.lD, A.lCW, A.lCR, A.wA, A.aD, A.lAR, A.lK, A.lT]

/-- **The contract of `postTransaction`**: with a new transaction id, it returns `false` and the
state holds `Model.St.post` (only the objects `PtMod` change); with an id already written, it
returns `true` (abended) and the state holds the outputs of `dupSt`. -/
def postTransactionSpec : Spec := Spec.of
  (fun args σ => ∃ p : PG, args = p.args ∧ PtFacts σ p)
  (fun args σ r σ' => ∀ p : PG, args = p.args → PtFacts σ p →
     (Model.tId p.t ∉ p.s.tranW.map Model.tId →
       r = some (.int 0) ∧ W σ' p.A (p.s.post p.clk p.t p.x p.a) ∧ FrameS σ σ' (PtMod p.A) ∧
       (∃ xs, σ'.heap p.A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs))) ∧
     (Model.tId p.t ∈ p.s.tranW.map Model.tId →
       r = some (.int 1) ∧ WAb σ' p.A (dupSt p.s p.t p.x p.a)) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

abbrev postTransactionRef : MethodRef :=
  Gen.Cbtrn02c.«postTransaction(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,java.lang.String,Cbtrn02c$CardXrefRecord,Cbtrn02c$AccountRecord,Cbtrn02c$TranCatBalRecord,Cbtrn02c$TranRecord,Cbtrn02c$AccountRecord[],java.util.List,java.util.List)».ref

def postTransactionSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .boolean, "postTransaction", [.cls "Cbtrn02c$Result",
    .cls "Cbtrn02c$DalytranRecord", .cls "java.lang.String", .cls "Cbtrn02c$CardXrefRecord",
    .cls "Cbtrn02c$AccountRecord", .cls "Cbtrn02c$TranCatBalRecord", .cls "Cbtrn02c$TranRecord",
    .array (.cls "Cbtrn02c$AccountRecord"), .cls "java.util.List", .cls "java.util.List"]⟩

/-- The locals of `postTransaction` after its parameters: `r0` `Result`, `r1` the transaction,
`r3`–`r6` the work-storage records, `r7` the account table, `r8` the category list, `r9` the
id list. -/
def PtLocs (p : PG) (fr : Frame) : Prop :=
  fr.get 4 = some (.ref p.A.r) ∧ fr.get 2 = some (.ref p.d) ∧ fr.get 8 = some (.ref p.A.wX) ∧
  fr.get 5 = some (.ref p.A.wA) ∧ fr.get 1 = some (.ref p.A.wC) ∧ fr.get 11 = some (.ref p.A.wT) ∧
  fr.get 0 = some (.ref p.A.aD) ∧ fr.get 6 = some (.ref p.A.lC) ∧ fr.get 7 = some (.ref p.A.lK)

/-- Statement 36: `tranWs` holds the record to write. -/
def Pt36 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ p : PG, args = p.args → PtFacts σ0 p →
    PtLocs p fr ∧ W σ p.A p.s ∧ FrameS σ0 σ [p.A.wT] ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    JRecAt TranRecord trCls σ (.ref p.A.wT) (Model.tranVals p.t p.clk)

/-- Statement 39: the category balance updated. -/
def Pt39 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ p : PG, args = p.args → PtFacts σ0 p →
    PtLocs p fr ∧ W σ p.A (postCat p.s p.t p.x) ∧
    FrameS σ0 σ [p.A.wT, p.A.wC, p.A.lC, p.A.lD, p.A.lCW, p.A.lCR] ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    JRecAt TranRecord trCls σ (.ref p.A.wT) (Model.tranVals p.t p.clk)

/-- Statement 40: the account updated. -/
def Pt40 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ p : PG, args = p.args → PtFacts σ0 p →
    PtLocs p fr ∧ W σ p.A (postAcc (postCat p.s p.t p.x) p.t p.a) ∧
    FrameS σ0 σ [p.A.wT, p.A.wC, p.A.lC, p.A.lD, p.A.lCW, p.A.lCR, p.A.wA, p.A.aD, p.A.lAR] ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    JRecAt TranRecord trCls σ (.ref p.A.wT) (Model.tranVals p.t p.clk) ∧
    (∃ xs, σ.heap p.A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs))

def ptInv : Invariants := [(36, Pt36), (39, Pt39), (40, Pt40)]

end EquivLean.Modernize.Cbtrn02c.Java
