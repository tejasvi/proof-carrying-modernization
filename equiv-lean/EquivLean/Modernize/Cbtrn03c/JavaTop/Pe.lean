import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processEnd`, definitions

`processEnd(ws, tran)` is `Model.eofTail`: the two displays and the additions to the totals
(segment `PeEntry`, statements 0–19), then `writePageTotals` (statement 20) and
`writeGrandTotals` (statement 21) on their model contracts.  One cut at each of the two calls:
the contracts' premises are then hypotheses of the call's state.  The ghost values (`w c d s t`)
are parameters (`peSpecG`); `pe_sat` quantifies them (`processEndSpecM`).

Locals: `r0` (the `Ws` object) 1, `r1` (the record) 5.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

abbrev peRef : MethodRef := Gen.Cbtrn03c.«processEnd(Cbtrn03c$Ws,Cbtrn03c$TranRecord)».ref

def zonedSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "zoned", [.prim .long, .prim .int]⟩
def add11Sig : MethodSig := ⟨"Cbtrn03c", .prim .long, "add11", [.prim .long, .prim .long]⟩

/-- `zoned(v, n)`: the model's signed DISPLAY field. -/
def zonedSpecT : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 1 ≤ n.toInt ∧ n.toInt ≤ 18 ∧
     σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (jline (Model.zoned n.toInt.toNat v.toInt))) ∧
       σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `add11(a, b)` (cir-repin's `add11Spec`). -/
def add11SpecT : Spec := Spec.of
  (fun args _ => ∃ a b : I64, args = [.long a, .long b])
  (fun args σ r σ' => ∀ a b : I64, args = [.long a, .long b] →
     r = some (.long ((a + b).srem (BitVec.ofInt 64 100000000000))) ∧ σ' = σ)

def peCallees : Contracts :=
  [(zonedSig, zonedSpecT), (add11Sig, add11SpecT), (writePageTotalsSig, writePageTotalsSpecM),
   (writeGrandTotalsSig, writeGrandTotalsSpecM)]

/-- The model state at statement 20: the two lines displayed, the last amount added. -/
def peS1 (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal) : Model.St :=
  { Model.dsp (Model.dsp s (Model.txt "TRAN-AMT " ++ Model.zoned 11 (Model.tAmt t)))
      (Model.txt "WS-PAGE-TOTAL" ++ Model.zoned 11 s.page) with
    page := Model.trunc11 (s.page + Model.tAmt t), acct := Model.trunc11 (s.acct + Model.tAmt t) }

theorem eofTail_eq (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal) :
    Model.eofTail s t = Model.grandTotals (Model.pageTotals (peS1 s t)) := rfl

/-- `processEnd` for given ghost values. -/
def peSpecG (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : Spec :=
  Spec.of
  (fun args σ => args = [.ref w, .ref c] ∧ WsRel σ w ld lr d s ∧ TranFields σ c t ∧
     (Model.tAmt t).natAbs < 100000000000 ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => r = none ∧ WsRel σ' w ld lr d (Model.eofTail s t) ∧ KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The cuts: at each call, the model state it starts from. -/
def peInv (w ld lr : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : Invariants :=
  [(20, fun _ σ0 fr σ => fr.get 1 = some (.ref w) ∧ WsRel σ w ld lr d (peS1 s t) ∧
      KeepsNonWs σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf fdC = .done),
   (21, fun _ σ0 fr σ => fr.get 1 = some (.ref w) ∧
      WsRel σ w ld lr d (Model.pageTotals (peS1 s t)) ∧
      KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done)]

/-- The paths of `processEnd` from statement `pc`. -/
def peWP (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog peCallees.env 0)
    Gen.Cbtrn03c.«processEnd(Cbtrn03c$Ws,Cbtrn03c$TranRecord)»
    ((peInv w ld lr d t s).inst args σ0) ((peSpecG w ld lr c d t s).post args σ0) 100 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java.Top
