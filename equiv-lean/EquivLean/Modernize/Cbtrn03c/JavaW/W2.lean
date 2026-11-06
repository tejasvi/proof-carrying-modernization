import EquivLean.Modernize.Cbtrn03c.JavaW.W
import EquivLean.Modernize.Cbtrn03c.JavaW.Edit
import EquivLean.Modernize.Cbtrn03c.JavaW.TotDefs

/-!
# CBTRN03C → Java: `writePageTotals`, the contract and its cuts

Against the contracts of `pad`, `repeat`, `edit`, `add11`, `writeLine`, `incLine`.  The ghost
values (the `Ws` object `w`, its lists `ld`, `lr`, its fields `v`) are parameters; one cut at each
`writeLine` call (statements 11, 19), where the state is described afresh.  The segments are in
`W2a`, `W2b`, `W2c`; `W2v` puts them together.

Locals: `r0` (the `Ws` object) 0, `$r2` (the line) 4.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ## Callees -/

def editSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "edit", [.prim .long, .prim .boolean]⟩
def add11Sig : MethodSig := ⟨"Cbtrn03c", .prim .long, "add11", [.prim .long, .prim .long]⟩

theorem edit_sat : Sat Gen.prog editRef editSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [editCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨spaces_ok, digits_ok⟩)) edit_vc

set_option maxHeartbeats 0 in
theorem edit_ok : ContractOK Gen.prog editSig editSpec := by
  jcontract_ok [edit_sat]

theorem add11_sat : Sat Gen.prog add11Ref add11Spec := add11_vc.sat

set_option maxHeartbeats 0 in
theorem add11_ok : ContractOK Gen.prog add11Sig add11Spec := by
  jcontract_ok [add11_sat]

def totalsCallees : Contracts :=
  [(padSig, padSpecF), (repeatSig, repeatSpec), (editSig, editSpec), (add11Sig, add11Spec),
   (writeLineSig, writeLineSpec), (incLineSig, incLineSpec)]

theorem totalsCallees_valid : Valid Gen.prog totalsCallees.env := by
  apply Contracts.valid_of_ok
  simp only [totalsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨padF_ok, repeat_ok, edit_ok, add11_ok, writeLine_ok, incLine_ok⟩

/-! ## Lengths -/

theorem fixJ_length (s : JStr) (n : Nat) : (fixJ s n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fixJ, ih]

theorem edS9_length (D : JStr) : (edS D 9).length = 11 := by
  simp [edS]

theorem editJ_length (neg plus : Bool) (m : Nat) : (editJ neg plus m).length = 15 := by
  unfold editJ
  split
  · exact spJ_length 15
  · simp [edS9_length]

theorem totalLineJ_length (l : JStr) (w n : Nat) (v : I64) :
    (totalLineJ l w n v).length = w + n + 15 := by
  simp [totalLineJ, fixJ_length, repJ_length, editJ_length]
  omega

/-! ## `writePageTotals` -/

abbrev writePageTotalsRef : MethodRef := Gen.Cbtrn03c.«writePageTotals(Cbtrn03c$Ws)».ref

/-- The fields after the page total line: the total added to the grand total and reset, the
counter incremented. -/
def page1V (v : WsV) (r1 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1]
    grand := add11J v.grand v.page
    page := 0#64
    lc := incL v.lc }

/-- The fields after both lines. -/
def page2V (v : WsV) (r1 r2 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1] ++ [r2]
    grand := add11J v.grand v.page
    page := 0#64
    lc := incL (incL v.lc) }

/-- `writePageTotals` for given ghost values. -/
def writePageTotalsSpecG (w ld lr : Addr) (v : WsV) : Spec := Spec.of
  (fun args σ => args = [.ref w] ∧ WsAt σ w ld lr v ∧ -9223372036854775808 < v.page.toInt ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∃ r1 r2 f1 f2 z1 z2, r = none ∧
     WsAt σ' w ld lr (page2V v (.ref r1) (.ref r2)) ∧
     σ'.heap r1 = some (.plain fdC f1) ∧ Fields.get f1 (fdC, "fdReptfileRec") = some (.ref z1) ∧
     σ'.heap z1 = some (.str (fixJ (totalLineJ (JStr.ofString "Page Total") 11 86 v.page) 133)) ∧
     σ'.heap r2 = some (.plain fdC f2) ∧ Fields.get f2 (fdC, "fdReptfileRec") = some (.ref z2) ∧
     σ'.heap z2 = some (.str (fixJ dashJ 133)) ∧
     Frame3 σ σ' w ld lr ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the first `writeLine` (statement 11): the line built, the working state as at the entry. -/
def wptI1 (w ld lr : Addr) (v : WsV) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y, fr.get 0 = some (.ref w) ∧ fr.get 4 = some (.ref y) ∧
    σ.heap y = some (.str (totalLineJ (JStr.ofString "Page Total") 11 86 v.page)) ∧
    WsAt σ w ld lr v ∧ Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the second `writeLine` (statement 19): the dashes built, the first line written. -/
def wptI2 (w ld lr : Addr) (v : WsV) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y r1 f1 z1, fr.get 0 = some (.ref w) ∧ fr.get 4 = some (.ref y) ∧
    σ.heap y = some (.str dashJ) ∧ WsAt σ w ld lr (page1V v (.ref r1)) ∧
    σ.heap r1 = some (.plain fdC f1) ∧ Fields.get f1 (fdC, "fdReptfileRec") = some (.ref z1) ∧
    σ.heap z1 = some (.str (fixJ (totalLineJ (JStr.ofString "Page Total") 11 86 v.page) 133)) ∧
    σ0.next ≤ r1 ∧ σ0.next ≤ z1 ∧ w < σ0.next ∧ lr < σ0.next ∧
    Frame3 σ0 σ w ld lr ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def writePageTotalsInv (w ld lr : Addr) (v : WsV) : Invariants :=
  [(11, fun _ σ0 fr σ => wptI1 w ld lr v σ0 fr σ),
   (19, fun _ σ0 fr σ => wptI2 w ld lr v σ0 fr σ)]

/-- The paths of `writePageTotals` from statement `pc`. -/
def wptWP (w ld lr : Addr) (v : WsV) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame)
    (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog totalsCallees.env 0)
    Gen.Cbtrn03c.«writePageTotals(Cbtrn03c$Ws)»
    ((writePageTotalsInv w ld lr v).inst args σ0) ((writePageTotalsSpecG w ld lr v).post args σ0)
    80 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java
