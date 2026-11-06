-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermWDefs.lean (sha256 cd429a0a2e289dae...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W2
import EquivLean.Modernize.Cbtrn03c.JavaW.W3
import EquivLean.Modernize.Cbtrn03c.JavaW.W4
import EquivLean.Modernize.Cbtrn03c.JavaW.W5
import EquivLean.Modernize.TermCommon

/-!
# CBTRN03C → Java: definitions for the termination of the working-state writers

The thin paths of the six writers (`writePageTotals`, `writeAccountTotals`, `writeGrandTotals`,
`writeHeaders`, `writeDetail`, `writeTransactionReport`), with their `MethodVC`s' invariants; their
cut points are straight-line, the variant `1000 - pc`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- Straight-line cut points: `1000 - pc`. -/
def wLineVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat := 1000 - pc

def wptThinWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writePageTotals(Cbtrn03c$Ws)»
    ((writePageTotalsInv w ld lr v).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 80 pc fr σ

def wptThinWP0 (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writePageTotals(Cbtrn03c$Ws)»
    ((writePageTotalsInv w ld lr v).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 80 0
    (Frame.init true args) σ0

def watThinWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writeAccountTotals(Cbtrn03c$Ws)»
    ((writeAccountTotalsInv w ld lr v).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 80 pc fr σ

def watThinWP0 (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writeAccountTotals(Cbtrn03c$Ws)»
    ((writeAccountTotalsInv w ld lr v).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 80 0
    (Frame.init true args) σ0

def wgtThinWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writeGrandTotals(Cbtrn03c$Ws)»
    ((writeGrandTotalsInv w ld lr v).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 80 pc fr σ

def wgtThinWP0 (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog totalsCallees.env 0) Gen.Cbtrn03c.«writeGrandTotals(Cbtrn03c$Ws)»
    ((writeGrandTotalsInv w ld lr v).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 80 0
    (Frame.init true args) σ0

def whThinWP (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog linesCallees.env 0) Gen.Cbtrn03c.«writeHeaders(Cbtrn03c$Ws)»
    ((writeHeadersInv w ld lr v rs re).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 120 pc fr σ

def whThinWP0 (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog linesCallees.env 0) Gen.Cbtrn03c.«writeHeaders(Cbtrn03c$Ws)»
    ((writeHeadersInv w ld lr v rs re).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 120 0
    (Frame.init true args) σ0

def wdThinWP (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog linesCallees.env 0)
    Gen.Cbtrn03c.«writeDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((writeDetailInv w ld lr v c yx cx t ys cs).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 120 pc fr σ

def wdThinWP0 (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog linesCallees.env 0)
    Gen.Cbtrn03c.«writeDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((writeDetailInv w ld lr v c yx cx t ys cs).map fun p => (p.1, fun _ _ => True)) (fun _ => True)
    120 0 (Frame.init true args) σ0

def wtrThinWP (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat)
    (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog reportCalleesR.env 0)
    Gen.Cbtrn03c.«writeTransactionReport(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((wtrInv w ld lr c ty ca d s t y cc).map fun q => (q.1, fun fr' σ' =>
      wLineVs q.1 args σ0 fr' σ' < wLineVs pc args σ0 fr σ)) (fun _ => True) 100 pc fr σ

def wtrThinWP0 (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog reportCalleesR.env 0)
    Gen.Cbtrn03c.«writeTransactionReport(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((wtrInv w ld lr c ty ca d s t y cc).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 100 0
    (Frame.init true args) σ0

end EquivLean.Modernize.Cbtrn03c.Java
