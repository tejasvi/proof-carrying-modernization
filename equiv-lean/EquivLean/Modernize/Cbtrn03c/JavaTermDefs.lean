-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermDefs.lean (sha256 686a24cc4dbc0b14...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.TermCommon

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: definitions for the termination of the top layer

The split VC (`Jimple.TermVC.of_thin`) with the invariants of `run_vc`, `pd_vc`, `pe_vc`.
* `run` (cut points 34, 35, 52, 53, 56): the read loop's measure `runOuter` (twice the records
  not yet read, of at most `2^31`, plus one until `eof` is set); in an iteration 35 → 52 → 53 → 35
  the weights `4·m + 1`, `4·m + 3`, `4·m + 2` (a read takes 2 from `m`); `processEnd` (56) is
  called with `eof` just set and returns to the loop head, weight `4·m + 2`; 34 above all.
* `processDetail` and `processEnd`: their cut points are straight-line, the variant `1000 - pc`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- The read loop's measure: `$i0` (records read, local 1), `eof` (`z3`, local 9). -/
def runOuter (fr : Frame) : Nat :=
  match fr.get 1, fr.get 9 with
  | some (.int i), some (.int z) => 2 * (2147483648 - i.toInt).toNat + (if z = 0 then 1 else 0)
  | _, _ => 0

/-- The variants of `run`'s cut points. -/
def runVs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 34 then 17179869193
  else if pc = 35 then 4 * runOuter fr + 1
  else if pc = 52 then 4 * runOuter fr + 3
  else if pc = 53 then 4 * runOuter fr + 2
  else if pc = 56 then 4 * runOuter fr + 2
  else 0

/-- The thin paths of `run` from cut point `pc`. -/
def runThinWP (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs) (args : List Value)
    (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBody
    ((runInv a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).map fun q => (q.1, fun fr' σ' =>
      runVs q.1 args σ0 fr' σ' < runVs pc args σ0 fr σ))
    (fun _ => True) 200 pc fr σ

/-- The thin entry path of `run`. -/
def runThinWP0 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs) (args : List Value)
    (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBody
    ((runInv a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).map fun p => (p.1, fun _ _ => True))
    (fun _ => True) 200 0 (Frame.init true args) σ0

/-- The variants of `processDetail`'s and `processEnd`'s (straight-line) cut points. -/
def lineVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat := 1000 - pc

/-- The thin paths of `processDetail` from cut point `pc`. -/
def pdThinWP (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog pdCallees.env 0)
    Gen.Cbtrn03c.«processDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,Cbtrn03c$CardXrefRecord[],Cbtrn03c$TranTypeRecord[],Cbtrn03c$TranCatRecord[])»
    ((pdInv w ld lr c a2 a3 a4 d t s xs ys cs).map fun q => (q.1, fun fr' σ' =>
      lineVs q.1 args σ0 fr' σ' < lineVs pc args σ0 fr σ))
    (fun _ => True) 120 pc fr σ

/-- The thin entry path of `processDetail`. -/
def pdThinWP0 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog pdCallees.env 0)
    Gen.Cbtrn03c.«processDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,Cbtrn03c$CardXrefRecord[],Cbtrn03c$TranTypeRecord[],Cbtrn03c$TranCatRecord[])»
    ((pdInv w ld lr c a2 a3 a4 d t s xs ys cs).map fun p => (p.1, fun _ _ => True))
    (fun _ => True) 120 0 (Frame.init true args) σ0

/-- The thin paths of `processEnd` from cut point `pc`. -/
def peThinWP (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog peCallees.env 0)
    Gen.Cbtrn03c.«processEnd(Cbtrn03c$Ws,Cbtrn03c$TranRecord)»
    ((peInv w ld lr d t s).map fun q => (q.1, fun fr' σ' =>
      lineVs q.1 args σ0 fr' σ' < lineVs pc args σ0 fr σ))
    (fun _ => True) 100 pc fr σ

/-- The thin entry path of `processEnd`. -/
def peThinWP0 (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog peCallees.env 0)
    Gen.Cbtrn03c.«processEnd(Cbtrn03c$Ws,Cbtrn03c$TranRecord)»
    ((peInv w ld lr d t s).map fun p => (p.1, fun _ _ => True))
    (fun _ => True) 100 0 (Frame.init true args) σ0

end EquivLean.Modernize.Cbtrn03c.Java.Top
