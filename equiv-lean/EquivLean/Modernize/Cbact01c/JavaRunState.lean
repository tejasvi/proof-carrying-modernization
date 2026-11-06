import EquivLean.Modernize.Cbact01c.JavaRunWVbrc

/-!
# CBACT01C → Java: definitions for the proof of `run`

The contract `runSpecG σ0 a vals` fixes the entry state `σ0`, the input array `a` and the field
values `vals` of its records: the `Result` is then the object at `B = σ0.next` and its four lists
(`displays`, `outFileWrites`, `arryFileWrites`, `vbrcFileWrites`) are at `B + 1` … `B + 4`.
The record methods are answered by contracts for these lists (`*SpecR`), stated against the
records of `σ0`: `AcctOk σ0 c` with the heap grown from `σ0` (`Grows σ0 σ`).

One cut point, the head of the read loop (statement 10, `LoopAt`): `k` records read, the
outputs those of `Model` after them (`mst vals k`).

Locals of `run`: `$r1` 0 (the `Result`), `r0` 1 (the array), `$l1` 2, `l3` 3 (`outCycDebit`),
`$r2` 4, `$b2` 5, `$i0` 6, `i4` 7 (`pos`), `$r3` 8, `r10` 9 (`codatecnOutDate`), `r11` 10 (the
record), `$z0` 11 (`endOfFile`), `z1` 12 (`pastEnd`), `$z3` 13.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-! ## The record methods, for the lists of the `Result` -/

def displayAcctRecordSig : MethodSig :=
  ⟨"Cbact01c", .void, "displayAcctRecord", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩
def writeOutRecordSig : MethodSig :=
  ⟨"Cbact01c", .void, "writeOutRecord",
    [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord", .cls "java.lang.String", .prim .long]⟩
def writeArrayRecordSig : MethodSig :=
  ⟨"Cbact01c", .void, "writeArrayRecord", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩
def writeVbrcRecordsSig : MethodSig :=
  ⟨"Cbact01c", .void, "writeVbrcRecords", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩
def accountRecordTextSig : MethodSig :=
  ⟨"Cbact01c", .cls "java.lang.String", "accountRecordText", [.cls "Cbact01c$AccountRecord"]⟩
def cobdatftSig : MethodSig :=
  ⟨"Cbact01c", .cls "java.lang.String", "cobdatft",
    [.cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"]⟩

/-- `displayAcctRecord(res, c)`, `L` the `displays` list of `res`, the record of `σ0`. -/
def displayAcctRecordSpecR (σ0 : Jimple.State) (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys m, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "displays") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ Hide (AcctOk σ0 c) ∧ Grows σ0 σ ∧ σ0.next + 4 < σ.next ∧
     σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : Addr,
       σ'.heap L = some (.list .arrayList (lElems σ L ++
         [.ref w1, .ref w2, .ref w3, .ref w4, .ref w5, .ref w6, .ref w7, .ref w8, .ref w9, .ref w10,
          .ref w11, .ref w12]) (lMods σ L + 12)) ∧
       σ.next ≤ w1 ∧ σ.next ≤ w2 ∧ σ.next ≤ w3 ∧ σ.next ≤ w4 ∧ σ.next ≤ w5 ∧ σ.next ≤ w6 ∧
       σ.next ≤ w7 ∧ σ.next ≤ w8 ∧ σ.next ≤ w9 ∧ σ.next ≤ w10 ∧ σ.next ≤ w11 ∧ σ.next ≤ w12 ∧
       σ'.heap w1 = some (.str (dispLine σ0 c 0)) ∧ σ'.heap w2 = some (.str (dispLine σ0 c 1)) ∧
       σ'.heap w3 = some (.str (dispLine σ0 c 2)) ∧ σ'.heap w4 = some (.str (dispLine σ0 c 3)) ∧
       σ'.heap w5 = some (.str (dispLine σ0 c 4)) ∧ σ'.heap w6 = some (.str (dispLine σ0 c 5)) ∧
       σ'.heap w7 = some (.str (dispLine σ0 c 6)) ∧ σ'.heap w8 = some (.str (dispLine σ0 c 7)) ∧
       σ'.heap w9 = some (.str (dispLine σ0 c 8)) ∧ σ'.heap w10 = some (.str (dispLine σ0 c 9)) ∧
       σ'.heap w11 = some (.str (dispLine σ0 c 10)) ∧
       σ'.heap w12 = some (.str (dispLine σ0 c 11))) ∧
     σ.next ≤ σ'.next ∧ σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `writeOutRecord(res, c, d, cd)`, `L` the `outFileWrites` list of `res`.  The postcondition
matches on the arguments (no quantified argument equation for the symbolic execution to
instantiate). -/
def writeOutRecordSpecR (σ0 : Jimple.State) (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c d cd fs ys m sd, args = [.ref res, .ref c, .ref d, .long cd] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "outFileWrites") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ Hide (AcctOk σ0 c) ∧ Grows σ0 σ ∧ σ0.next + 4 < σ.next ∧
     σ.heap d = some (.str sd) ∧ sd.length < 2147483648 ∧ d ≠ L ∧
     σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$OutAcctRec" = .done)
  (fun args σ r σ' => match args with
   | [.ref _, .ref c, .ref d, .long cd] =>
     r = none ∧
     (∃ o, σ'.heap L = some (.list .arrayList (lElems σ L ++ [.ref o]) (lMods σ L + 1)) ∧
       σ.next ≤ o ∧ OutRecJ σ' o σ0 c (argText σ (.ref d)) cd σ.next) ∧
     σ.next ≤ σ'.next ∧ σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics
   | _ => True)

/-- `writeArrayRecord(res, c)`, `L` the `arryFileWrites` list of `res`. -/
def writeArrayRecordSpecR (σ0 : Jimple.State) (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys m, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "arryFileWrites") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ Hide (AcctOk σ0 c) ∧ Grows σ0 σ ∧ σ0.next + 4 < σ.next ∧
     σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$ArrArrayRec" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ o, σ'.heap L = some (.list .arrayList (lElems σ L ++ [.ref o]) (lMods σ L + 1)) ∧
       σ.next ≤ o ∧ ArrRecJ σ' o σ0 c σ.next) ∧
     σ.next ≤ σ'.next ∧ σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `writeVbrcRecords(res, c)`, `L1` / `L4` the `displays` / `vbrcFileWrites` lists of `res`. -/
def writeVbrcRecordsSpecR (σ0 : Jimple.State) (L1 L4 : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys1 m1 ys4 m4, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "displays") = some (.ref L1) ∧
     Fields.get fs (resCls, "vbrcFileWrites") = some (.ref L4) ∧ res < L1 ∧
     σ.heap L1 = some (.list .arrayList ys1 m1) ∧ σ.heap L4 = some (.list .arrayList ys4 m4) ∧
     Hide (AcctOk σ0 c) ∧ Grows σ0 σ ∧ σ0.next + 4 < σ.next ∧ σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ y1 y2 : Addr,
       σ'.heap L1 = some (.list .arrayList (lElems σ L1 ++ [.ref y1, .ref y2]) (lMods σ L1 + 2)) ∧
       σ.next ≤ y1 ∧ σ.next ≤ y2 ∧
       σ'.heap y1 = some (.str (JStr.ofString "VBRC-REC1:" ++ vb1J σ0 c)) ∧
       σ'.heap y2 = some (.str (JStr.ofString "VBRC-REC2:" ++ vb2J σ0 c))) ∧
     (∃ w1 w2 : Addr,
       σ'.heap L4 = some (.list .arrayList (lElems σ L4 ++ [.ref w1, .ref w2]) (lMods σ L4 + 2)) ∧
       σ.next ≤ w1 ∧ σ.next ≤ w2 ∧
       σ'.heap w1 = some (.str (vb1J σ0 c)) ∧ σ'.heap w2 = some (.str (vb2J σ0 c))) ∧
     σ.next ≤ σ'.next ∧ σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ (∀ x, x < σ.next → x ≠ L1 → x ≠ L4 → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `accountRecordText(c)`, the record of `σ0`. -/
def accountRecordTextSpecR (σ0 : Jimple.State) : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ Hide (AcctOk σ0 c) ∧ Grows σ0 σ ∧ σ0.next + 4 < σ.next ∧ σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (acctTextJ σ0 c)) ∧ σ.next ≤ x ∧
       σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `pad`, keeping the `Result` lists below the next address. -/
def padSpecR (σ0 : Jimple.State) : Spec := Spec.of
  (fun args σ => padSpec.pre args σ ∧ σ0.next + 4 < σ.next ∧ Grows σ0 σ ∧
     σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `cobdatft`, keeping the `Result` lists below the next address. -/
def cobdatftSpecR (σ0 : Jimple.State) : Spec := Spec.of
  (fun args σ => cobdatftSpec.pre args σ ∧ σ0.next + 4 < σ.next ∧ Grows σ0 σ ∧
     σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => match args with
   | [.ref _, .ref x2, .ref _, .ref x4] =>
     ∃ x, r = some (.ref x) ∧
       σ'.heap x = some (.str (cobOut (argText σ (.ref x2)) (argText σ (.ref x4)))) ∧
       σ.next ≤ x ∧ σ0.next + 4 < σ'.next ∧ Grows σ0 σ' ∧ σ'.initOf "Cbact01c" = .done ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics
   | _ => True)

/-- The callee contracts of `run` (`B = σ0.next`). -/
def runCallees (σ0 : Jimple.State) : Contracts :=
  [(spacesSig, spacesSpecF), (padSig, padSpecR σ0), (cobdatftSig, cobdatftSpecR σ0),
   (displayAcctRecordSig, displayAcctRecordSpecR σ0 (σ0.next + 1)),
   (writeOutRecordSig, writeOutRecordSpecR σ0 (σ0.next + 2)),
   (writeArrayRecordSig, writeArrayRecordSpecR σ0 (σ0.next + 3)),
   (writeVbrcRecordsSig, writeVbrcRecordsSpecR σ0 (σ0.next + 1) (σ0.next + 4)),
   (accountRecordTextSig, accountRecordTextSpecR σ0)]

/-- The callee environment of `run`: the contracts, looked up only for methods of `Cbact01c` (one
class-name comparison for every library call, instead of one per contract). -/
def runEnv (σ0 : Jimple.State) : SpecEnv := fun sig =>
  if sig.cls = "Cbact01c" then (runCallees σ0).env sig else none

theorem runEnv_valid {σ0 : Jimple.State} (h : Valid Gen.prog (runCallees σ0).env) :
    Valid Gen.prog (runEnv σ0) := by
  intro sig S hS
  by_cases hc : sig.cls = "Cbact01c"
  · simp only [runEnv, hc, ↓reduceIte] at hS
    exact h sig S hS
  · simp only [runEnv, hc, ↓reduceIte] at hS
    cases hS

/-! The lookups of the calls of `run`'s loop body, by evaluation (`rfl`): the symbolic execution
uses these equations instead of deciding the method signatures' strings itself. -/

theorem runEnv_listAdd (σ0 : Jimple.State) :
    runEnv σ0 ⟨"java.util.List", .prim .boolean, "add", [.cls "java.lang.Object"]⟩ = none := rfl
theorem runEnv_strEquals (σ0 : Jimple.State) :
    runEnv σ0 ⟨"java.lang.String", .prim .boolean, "equals", [.cls "java.lang.Object"]⟩ = none := rfl
theorem runEnv_displayIoStatus (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .void, "displayIoStatus", [.cls "Cbact01c$Result", .cls "java.lang.String"]⟩ =
      none := rfl
theorem runEnv_pad (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .cls "java.lang.String", "pad", [.cls "java.lang.String", .prim .int]⟩ =
      some (padSpecR σ0) := rfl
theorem runEnv_cobdatft (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .cls "java.lang.String", "cobdatft",
      [.cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"]⟩ =
      some (cobdatftSpecR σ0) := rfl
theorem runEnv_displayAcctRecord (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .void, "displayAcctRecord", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩ =
      some (displayAcctRecordSpecR σ0 (σ0.next + 1)) := rfl
theorem runEnv_writeOutRecord (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .void, "writeOutRecord",
      [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord", .cls "java.lang.String", .prim .long]⟩ =
      some (writeOutRecordSpecR σ0 (σ0.next + 2)) := rfl
theorem runEnv_writeArrayRecord (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .void, "writeArrayRecord", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩ =
      some (writeArrayRecordSpecR σ0 (σ0.next + 3)) := rfl
theorem runEnv_writeVbrcRecords (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .void, "writeVbrcRecords", [.cls "Cbact01c$Result", .cls "Cbact01c$AccountRecord"]⟩ =
      some (writeVbrcRecordsSpecR σ0 (σ0.next + 1) (σ0.next + 4)) := rfl
theorem runEnv_accountRecordText (σ0 : Jimple.State) :
    runEnv σ0 ⟨"Cbact01c", .cls "java.lang.String", "accountRecordText", [.cls "Cbact01c$AccountRecord"]⟩ =
      some (accountRecordTextSpecR σ0) := rfl

/-! ## The contract of `run` with fixed ghost values -/

/-- The classes are initialized. -/
def Inits (σ : Jimple.State) : Prop :=
  σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$Result" = .done ∧
  σ.initOf "Cbact01c$AccountRecord" = .done ∧ σ.initOf "Cbact01c$ArrArrayRec" = .done ∧
  σ.initOf "Cbact01c$OutAcctRec" = .done

/-- The outcome of `run` for the field values `vals`: the outputs of `Model.run`. -/
def RunPost (vals : List (List EquivLean.Cobol.Rec.FVal)) (r : Option Value) (σ' : Jimple.State) :
    Prop :=
  let o := Model.run vals
  ∃ res fs, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact01c$Result" fs) ∧
    LinesOf σ' fs "displays" o.disp ∧
    ListOf σ' fs "outFileWrites" OutAcctRec "Cbact01c$OutAcctRec" o.outWrites ∧
    ListOccOf σ' fs "arryFileWrites" ArrArrayRec "Cbact01c$ArrArrayRec" o.arryWrites ∧
    LinesOf σ' fs "vbrcFileWrites" o.vbrcWrites ∧
    Fields.get fs ("Cbact01c$Result", "abended") = some (.int 0)

def runSpecG (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) : Spec :=
  Spec.of (fun args σ => σ = σ0 ∧ args = [.ref a] ∧ AcctfileFileAt σ a vals ∧
      (∀ v ∈ vals, AccountRecord.Valid v) ∧ Inits σ)
    (fun _ _ r σ' => RunPost vals r σ')

/-! ## The loop invariant -/

/-- The outputs after the first `k` records. -/
def mst (vals : List (List EquivLean.Cobol.Rec.FVal)) (k : Nat) : Model.St :=
  (vals.take k).foldl Model.step Model.init

/-- The facts at the loop head that the symbolic execution does not track: the cycle debit `cd`
and the outputs are those of the model after `k` records, the date `s` is eight characters then
twelve spaces. -/
def RunData (σ0 : Jimple.State) (vals : List (List EquivLean.Cobol.Rec.FVal)) (σ : Jimple.State)
    (k : Nat) (cd : I64) (s : JStr) (ys1 ys2 ys3 ys4 : List Value) : Prop :=
  cd = BitVec.ofInt 64 (mst vals k).cd ∧ s.length = 20 ∧ s.drop 8 = fixStr [] 12 ∧
  OutsB σ (σ0.next + 4) ys1 ys2 ys3 ys4 (mst vals k)

/-- The loop invariant of `run` (statement 10): `i` records read; `z0` (`endOfFile`) = `z1`
(`pastEnd`), set only when all records were read; `d` the string `codatecnOutDate`; the `Result`
at `σ0.next`, its lists at `σ0.next + 1` … `+ 4`. -/
def runInv10 (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (_args : List Value) (_σ0' : Jimple.State) (fr : Frame) (σ : Jimple.State) : Prop :=
  ∃ (et : JType) (xs : List Value) (i z1 z0 : I32) (cd : I64) (d : Addr) (s : JStr)
    (fs : List (FieldKey × Value)) (ys1 ys2 ys3 ys4 : List Value) (m1 m2 m3 m4 : Nat),
    σ0.heap a = some (.array et xs) ∧
    fr.get 0 = some (.ref σ0.next) ∧ fr.get 1 = some (.ref a) ∧
    fr.get 7 = some (.int i) ∧ fr.get 12 = some (.int z1) ∧ fr.get 11 = some (.int z0) ∧
    fr.get 3 = some (.long cd) ∧ fr.get 9 = some (.ref d) ∧ σ.heap d = some (.str s) ∧
    σ.heap σ0.next = some (.plain resCls fs) ∧
    σ.heap (σ0.next + 1) = some (.list .arrayList ys1 m1) ∧
    σ.heap (σ0.next + 2) = some (.list .arrayList ys2 m2) ∧
    σ.heap (σ0.next + 3) = some (.list .arrayList ys3 m3) ∧
    σ.heap (σ0.next + 4) = some (.list .arrayList ys4 m4) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ z1 = z0 ∧ (z0 = 0#32 ∨ z0 = 1#32) ∧
    (z0 ≠ 0#32 → i.toInt = xs.length) ∧
    d ≠ σ0.next + 1 ∧ d ≠ σ0.next + 2 ∧ d ≠ σ0.next + 3 ∧ d ≠ σ0.next + 4 ∧
    Fields.get fs (resCls, "displays") = some (.ref (σ0.next + 1)) ∧
    Fields.get fs (resCls, "outFileWrites") = some (.ref (σ0.next + 2)) ∧
    Fields.get fs (resCls, "arryFileWrites") = some (.ref (σ0.next + 3)) ∧
    Fields.get fs (resCls, "vbrcFileWrites") = some (.ref (σ0.next + 4)) ∧
    Fields.get fs (resCls, "abended") = some (.int 0) ∧
    Hide (RunData σ0 vals σ i.toNat cd s ys1 ys2 ys3 ys4) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

def runInv (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) :
    Invariants := [(10, runInv10 σ0 a vals)]

abbrev runBody := Gen.Cbact01c.«run(Cbact01c$AccountRecord[])»

/-- The paths of `run` from statement `pc` (frame `fr`, state `σ`). -/
def RunWP (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (pc : Nat) (fr : Frame) (σ : Jimple.State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog (runEnv σ0) 1) runBody
    ((runInv σ0 a vals).inst [.ref a] σ0) ((runSpecG σ0 a vals).post [.ref a] σ0) 200 pc fr σ

end EquivLean.Modernize.Cbact01c.Java
