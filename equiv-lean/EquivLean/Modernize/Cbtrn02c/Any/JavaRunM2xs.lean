import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# CBTRN02C → Java: `writeTransaction` on any input (a repeated id abends)

`writeTransaction(r, tranWs, tranKeys)`: when the id of `tranWs` is already in `tranKeys`,
`abend(r, "ERROR WRITING TO TRANSACTION FILE", "22")` displays the message, the file status
(`displayIoStatus(r, "22")`: `FILE STATUS IS: NNNN0022`) and `ABENDING PROGRAM`, sets
`r.abended`, and `writeTransaction` returns `true`; otherwise the id is added to `tranKeys`, a
copy of `tranWs` to `r.transactFileWrites`, and it returns `false`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev abKey : FieldKey := ("Cbtrn02c$Result", "abended")

abbrev dispIoRef : MethodRef :=
  Gen.Cbtrn02c.«displayIoStatus(Cbtrn02c$Result,java.lang.String)».ref

def dispIoSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "displayIoStatus", [.cls "Cbtrn02c$Result", .cls "java.lang.String"]⟩

/-- `displayIoStatus` on status `22`. -/
def dispIoSpec22 : Spec := Spec.of
  (fun args σ => ∃ (r s lD : Addr) (fsR : List (FieldKey × Value)) (ds : List Value) (mD : Nat),
     args = [.ref r, .ref s] ∧ σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧
     Fields.get fsR dispKey = some (.ref lD) ∧ σ.heap lD = some (.list .arrayList ds mD) ∧
     σ.heap s = some (.str (JStr.ofString "22")) ∧ σ.initOf "Cbtrn02c" = .done)
  (fun args σ _ σ' => ∀ (r s : Addr), args = [.ref r, .ref s] →
     ∃ (y : Addr) (mD' : Nat),
       σ'.heap (refField σ r dispKey) =
         some (.list .arrayList (listOf σ (refField σ r dispKey) ++ [.ref y]) mD') ∧
       σ'.heap y = some (.str (JStr.ofString "FILE STATUS IS: NNNN0022")) ∧ σ.next ≤ y ∧
       FrameS σ σ' [refField σ r dispKey] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

def abCallees22 : Contracts := [(dispIoSig, dispIoSpec22)]

/-- `abend` with status `22` (the only status of the calls on the domain). -/
def abendSpec22 : Spec := Spec.of
  (fun args σ => ∃ (r sM sS lD : Addr) (fsR : List (FieldKey × Value)) (msg : JStr)
       (ds : List Value) (mD : Nat),
     args = [.ref r, .ref sM, .ref sS] ∧ σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧
     (∃ ab, Fields.get fsR abKey = some ab) ∧
     Fields.get fsR dispKey = some (.ref lD) ∧ σ.heap lD = some (.list .arrayList ds mD) ∧
     σ.heap sM = some (.str msg) ∧ σ.heap sS = some (.str (JStr.ofString "22")) ∧
     σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$Result" = .done)
  (fun args σ _ σ' => ∀ (r sM sS : Addr), args = [.ref r, .ref sM, .ref sS] →
     ∃ (y2 y3 : Addr) (mD' : Nat),
       σ'.heap (refField σ r dispKey) = some (.list .arrayList
         (listOf σ (refField σ r dispKey) ++ [.ref sM, .ref y2, .ref y3]) mD') ∧
       σ'.heap y2 = some (.str (JStr.ofString "FILE STATUS IS: NNNN0022")) ∧
       σ'.heap y3 = some (.str (JStr.ofString "ABENDING PROGRAM")) ∧
       σ'.heap r = some (.plain "Cbtrn02c$Result" (Fields.set (fieldsOf σ r) abKey (.int 1))) ∧
       σ.next ≤ y2 ∧ σ.next ≤ y3 ∧ FrameS σ σ' [refField σ r dispKey, r] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

def wtCalleesX : Contracts :=
  [(findKeySig, findKeySpecF), (copyTranSig, copyTranSpecF), (abendSig, abendSpec22)]

/-- The index of the id of `tranWs` in `tranKeys` (`-1` when it is new). -/
def wtIdx (σ : State) (wT lK : Addr) : Int :=
  firstIdx (fun v => strOfV σ v == some (argText σ (fld σ wT trIdKey))) (listOf σ lK)

/-- `writeTransaction` as a function of the state at the call: a new id is written, a repeated
one abends (returns `true`). -/
def writeTransactionSpecX : Spec := Spec.of
  (fun args σ => ∃ (r wT lK : Addr) (fsR : List (FieldKey × Value)) (lT lD : Addr)
       (fsT : List (FieldKey × Value)) (sId : Addr) (idcs : JStr) (ks : List Value) (mK : Nat)
       (ts : List Value) (mT : Nat) (ds : List Value) (mD : Nat),
     args = [.ref r, .ref wT, .ref lK] ∧ σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧
     Fields.get fsR ltKey = some (.ref lT) ∧ Fields.get fsR dispKey = some (.ref lD) ∧
     (∃ ab, Fields.get fsR abKey = some ab) ∧
     σ.heap wT = some (.plain "Cbtrn02c$TranRecord" fsT) ∧ AllSome trKeys fsT ∧
     Fields.get fsT trIdKey = some (.ref sId) ∧
     σ.heap sId = some (.str idcs) ∧ σ.heap lK = some (.list .arrayList ks mK) ∧
     ks.length < 2147483648 ∧ StrShapes σ ks ∧
     σ.heap lT = some (.list .arrayList ts mT) ∧ σ.heap lD = some (.list .arrayList ds mD) ∧
     [lK, lT, lD].Nodup ∧ σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$TranRecord" = .done ∧
     σ.initOf "Cbtrn02c$Result" = .done)
  (fun args σ r' σ' => ∀ (r wT lK : Addr), args = [.ref r, .ref wT, .ref lK] →
     (wtIdx σ wT lK < 0 →
       r' = some (.int 0) ∧
       ∃ (y : Addr) (fsy : List (FieldKey × Value)) (mK' mT' : Nat),
         σ'.heap lK = some (.list .arrayList (listOf σ lK ++ [fld σ wT trIdKey]) mK') ∧
         σ'.heap (refField σ r ltKey) =
           some (.list .arrayList (listOf σ (refField σ r ltKey) ++ [.ref y]) mT') ∧ σ.next ≤ y ∧
         σ'.heap y = some (.plain "Cbtrn02c$TranRecord" fsy) ∧ SameFields trKeys fsy (fieldsOf σ wT) ∧
         FrameS σ σ' [lK, refField σ r ltKey]) ∧
     (0 ≤ wtIdx σ wT lK →
       r' = some (.int 1) ∧
       ∃ (y1 y2 y3 : Addr) (mD' : Nat),
         σ'.heap (refField σ r dispKey) = some (.list .arrayList
           (listOf σ (refField σ r dispKey) ++ [.ref y1, .ref y2, .ref y3]) mD') ∧
         σ'.heap y1 = some (.str (JStr.ofString "ERROR WRITING TO TRANSACTION FILE")) ∧
         σ'.heap y2 = some (.str (JStr.ofString "FILE STATUS IS: NNNN0022")) ∧
         σ'.heap y3 = some (.str (JStr.ofString "ABENDING PROGRAM")) ∧
         σ'.heap r = some (.plain "Cbtrn02c$Result" (Fields.set (fieldsOf σ r) abKey (.int 1))) ∧
         σ.next ≤ y1 ∧ σ.next ≤ y2 ∧ σ.next ≤ y3 ∧
         FrameS σ σ' [refField σ r dispKey, r]) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

abbrev wtBody := Gen.Cbtrn02c.«writeTransaction(Cbtrn02c$Result,Cbtrn02c$TranRecord,java.util.List)»

/-- The postcondition of `writeTransaction`, folded. -/
def wtPostX (args : List Value) (σ0 : State) : Outcome → Prop := writeTransactionSpecX.post args σ0

attribute [irreducible] wtPostX

/-- Symbolic execution of `writeTransaction`'s body from `pc`. -/
def WtWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog wtCalleesX.env 0) wtBody [] (wtPostX args σ0) 40 pc fr σ

attribute [irreducible] WtWP

end EquivLean.Modernize.Cbtrn02c.Java
