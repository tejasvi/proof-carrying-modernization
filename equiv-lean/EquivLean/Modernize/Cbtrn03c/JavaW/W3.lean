import EquivLean.Modernize.Cbtrn03c.JavaW.W2

/-!
# CBTRN03C → Java: `writeAccountTotals`, `writeGrandTotals`, the contracts and their cuts

As `writePageTotals` (`W2.lean`): the ghost values are parameters, one cut at each `writeLine`
call (`writeAccountTotals`: statements 11, 15; `writeGrandTotals`: statement 11).  Segments in
`W3a`, `W3b`, `W3c`; `W3v` puts them together.

Locals of both: `r0` (the `Ws` object) 0, `$r2` (the line) 3.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ## `writeAccountTotals` -/

abbrev writeAccountTotalsRef : MethodRef := Gen.Cbtrn03c.«writeAccountTotals(Cbtrn03c$Ws)».ref

/-- The fields after the account total line: the total reset, the counter incremented. -/
def acct1V (v : WsV) (r1 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1]
    acct := 0#64
    lc := incL v.lc }

/-- The fields after both lines. -/
def acct2V (v : WsV) (r1 r2 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1] ++ [r2]
    acct := 0#64
    lc := incL (incL v.lc) }

/-- `writeAccountTotals` for given ghost values. -/
def writeAccountTotalsSpecG (w ld lr : Addr) (v : WsV) : Spec := Spec.of
  (fun args σ => args = [.ref w] ∧ WsAt σ w ld lr v ∧ -9223372036854775808 < v.acct.toInt ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∃ r1 r2 f1 f2 z1 z2, r = none ∧
     WsAt σ' w ld lr (acct2V v (.ref r1) (.ref r2)) ∧
     σ'.heap r1 = some (.plain fdC f1) ∧ Fields.get f1 (fdC, "fdReptfileRec") = some (.ref z1) ∧
     σ'.heap z1 =
       some (.str (fixJ (totalLineJ (JStr.ofString "Account Total") 13 84 v.acct) 133)) ∧
     σ'.heap r2 = some (.plain fdC f2) ∧ Fields.get f2 (fdC, "fdReptfileRec") = some (.ref z2) ∧
     σ'.heap z2 = some (.str (fixJ dashJ 133)) ∧
     Frame3 σ σ' w ld lr ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the first `writeLine` (statement 11). -/
def watI1 (w ld lr : Addr) (v : WsV) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y, fr.get 0 = some (.ref w) ∧ fr.get 3 = some (.ref y) ∧
    σ.heap y = some (.str (totalLineJ (JStr.ofString "Account Total") 13 84 v.acct)) ∧
    WsAt σ w ld lr v ∧ Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the second `writeLine` (statement 15). -/
def watI2 (w ld lr : Addr) (v : WsV) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y r1 f1 z1, fr.get 0 = some (.ref w) ∧ fr.get 3 = some (.ref y) ∧
    σ.heap y = some (.str dashJ) ∧ WsAt σ w ld lr (acct1V v (.ref r1)) ∧
    σ.heap r1 = some (.plain fdC f1) ∧ Fields.get f1 (fdC, "fdReptfileRec") = some (.ref z1) ∧
    σ.heap z1 =
      some (.str (fixJ (totalLineJ (JStr.ofString "Account Total") 13 84 v.acct) 133)) ∧
    σ0.next ≤ r1 ∧ σ0.next ≤ z1 ∧ w < σ0.next ∧ lr < σ0.next ∧
    Frame3 σ0 σ w ld lr ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def writeAccountTotalsInv (w ld lr : Addr) (v : WsV) : Invariants :=
  [(11, fun _ σ0 fr σ => watI1 w ld lr v σ0 fr σ),
   (15, fun _ σ0 fr σ => watI2 w ld lr v σ0 fr σ)]

/-- The paths of `writeAccountTotals` from statement `pc`. -/
def watWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog totalsCallees.env 0)
    Gen.Cbtrn03c.«writeAccountTotals(Cbtrn03c$Ws)»
    ((writeAccountTotalsInv w ld lr v).inst args σ0)
    ((writeAccountTotalsSpecG w ld lr v).post args σ0) 80 pc fr σ

/-! ## `writeGrandTotals` -/

abbrev writeGrandTotalsRef : MethodRef := Gen.Cbtrn03c.«writeGrandTotals(Cbtrn03c$Ws)».ref

/-- The fields after the grand total line. -/
def grand1V (v : WsV) (r1 : Value) : WsV := { v with wrs := v.wrs ++ [r1] }

/-- `writeGrandTotals` for given ghost values. -/
def writeGrandTotalsSpecG (w ld lr : Addr) (v : WsV) : Spec := Spec.of
  (fun args σ => args = [.ref w] ∧ WsAt σ w ld lr v ∧ -9223372036854775808 < v.grand.toInt ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∃ r1 f1 z1, r = none ∧ WsAt σ' w ld lr (grand1V v (.ref r1)) ∧
     σ'.heap r1 = some (.plain fdC f1) ∧ Fields.get f1 (fdC, "fdReptfileRec") = some (.ref z1) ∧
     σ'.heap z1 =
       some (.str (fixJ (totalLineJ (JStr.ofString "Grand Total") 11 86 v.grand) 133)) ∧
     Frame3 σ σ' w ld lr ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the `writeLine` (statement 11). -/
def wgtI1 (w ld lr : Addr) (v : WsV) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y, fr.get 0 = some (.ref w) ∧ fr.get 3 = some (.ref y) ∧
    σ.heap y = some (.str (totalLineJ (JStr.ofString "Grand Total") 11 86 v.grand)) ∧
    WsAt σ w ld lr v ∧ Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def writeGrandTotalsInv (w ld lr : Addr) (v : WsV) : Invariants :=
  [(11, fun _ σ0 fr σ => wgtI1 w ld lr v σ0 fr σ)]

/-- The paths of `writeGrandTotals` from statement `pc`. -/
def wgtWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog totalsCallees.env 0)
    Gen.Cbtrn03c.«writeGrandTotals(Cbtrn03c$Ws)»
    ((writeGrandTotalsInv w ld lr v).inst args σ0)
    ((writeGrandTotalsSpecG w ld lr v).post args σ0) 80 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java
