import EquivLean.Modernize.Cbtrn03c.JavaTop.CalSpaces

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contract of `blankTran`

`blankTran()`: a new transaction record holding the record area's initial contents (spaces and
zeros), against the contract of `spaces` (`spaces_ok`); the constructor is inlined (depth 1).
One cut before each call (statements 1–12): the record object (fields as `new` leaves them), the
strings made so far, the frame.  Locals: `$r1` … `$r11` 0 … 10, `$r0` 11.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

abbrev blankTranRef : MethodRef := Gen.Cbtrn03c.«blankTran()».ref

def blankCallees : Contracts := [(spacesSig, spacesSpecT)]

/-- The cuts: before call `k` (statement `k`), the strings of the calls before it. -/
def blankInv : Invariants := [
  (1, fun _ σ0 fr σ => ∃ r0,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (2, fun _ σ0 fr σ => ∃ r0 y0,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (3, fun _ σ0 fr σ => ∃ r0 y0 y1,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (4, fun _ σ0 fr σ => ∃ r0 y0 y1 y2,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (5, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (6, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (7, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (8, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5 y6,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      fr.get 6 = some (.ref y6) ∧
      σ.heap y6 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y6 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (9, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5 y6 y7,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      fr.get 6 = some (.ref y6) ∧
      σ.heap y6 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y6 ∧
      fr.get 7 = some (.ref y7) ∧
      σ.heap y7 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y7 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (10, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5 y6 y7 y8,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      fr.get 6 = some (.ref y6) ∧
      σ.heap y6 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y6 ∧
      fr.get 7 = some (.ref y7) ∧
      σ.heap y7 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y7 ∧
      fr.get 8 = some (.ref y8) ∧
      σ.heap y8 = some (.str (cp037Str (Model.sp 26))) ∧
      r0 < y8 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (11, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      fr.get 6 = some (.ref y6) ∧
      σ.heap y6 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y6 ∧
      fr.get 7 = some (.ref y7) ∧
      σ.heap y7 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y7 ∧
      fr.get 8 = some (.ref y8) ∧
      σ.heap y8 = some (.str (cp037Str (Model.sp 26))) ∧
      r0 < y8 ∧
      fr.get 9 = some (.ref y9) ∧
      σ.heap y9 = some (.str (cp037Str (Model.sp 26))) ∧
      r0 < y9 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done),
  (12, fun _ σ0 fr σ => ∃ r0 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10,
      fr.get 11 = some (.ref r0) ∧
      σ.heap r0 = some (.plain tranC ((Gen.prog.instanceFields tranC).map fun p => (p.1, p.2.default))) ∧
      σ0.next ≤ r0 ∧
      fr.get 0 = some (.ref y0) ∧
      σ.heap y0 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y0 ∧
      fr.get 1 = some (.ref y1) ∧
      σ.heap y1 = some (.str (cp037Str (Model.sp 2))) ∧
      r0 < y1 ∧
      fr.get 2 = some (.ref y2) ∧
      σ.heap y2 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y2 ∧
      fr.get 3 = some (.ref y3) ∧
      σ.heap y3 = some (.str (cp037Str (Model.sp 100))) ∧
      r0 < y3 ∧
      fr.get 4 = some (.ref y4) ∧
      σ.heap y4 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y4 ∧
      fr.get 5 = some (.ref y5) ∧
      σ.heap y5 = some (.str (cp037Str (Model.sp 50))) ∧
      r0 < y5 ∧
      fr.get 6 = some (.ref y6) ∧
      σ.heap y6 = some (.str (cp037Str (Model.sp 10))) ∧
      r0 < y6 ∧
      fr.get 7 = some (.ref y7) ∧
      σ.heap y7 = some (.str (cp037Str (Model.sp 16))) ∧
      r0 < y7 ∧
      fr.get 8 = some (.ref y8) ∧
      σ.heap y8 = some (.str (cp037Str (Model.sp 26))) ∧
      r0 < y8 ∧
      fr.get 9 = some (.ref y9) ∧
      σ.heap y9 = some (.str (cp037Str (Model.sp 26))) ∧
      r0 < y9 ∧
      fr.get 10 = some (.ref y10) ∧
      σ.heap y10 = some (.str (cp037Str (Model.sp 20))) ∧
      r0 < y10 ∧
      σ0.next ≤ σ.next ∧
      Agree σ0 σ ∧
      σ.inits = σ0.inits ∧
      σ.statics = σ0.statics ∧
      σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf tranC = .done)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem blankTran_vc : MethodVC Gen.prog blankCallees.env 1 blankTranRef blankTranSpecT blankInv 80 := by
  jverify [blankTranSpecT, blankInv, blankCallees, spacesSig, spacesSpecT, Agree, TranFields, SFld,
    LFld, tranC, Model.tran0, Model.tId, Model.tType, Model.tCat, Model.tSource, Model.tAmt,
    Model.tCard, Model.strOf, Model.numOf, ite_nat_ne]
  all_goals first
    | (intro h; subst h; jomega)
    | skip

theorem blankTran_sat : Sat Gen.prog blankTranRef blankTranSpecT :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [blankCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact spaces_ok)) blankTran_vc

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem blankTran_ok : ContractOK Gen.prog blankTranSig blankTranSpecT := by
  jcontract_ok [Cal.blankTran_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.blankTran_ok
