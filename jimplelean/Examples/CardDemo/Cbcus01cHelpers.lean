/-
  Examples/CardDemo/Cbcus01cHelpers.lean

  The helpers of `Cbcus01c`: `spaces` and `fmtNum` have the bodies of CBACT02C's `spaces` and
  `zeroPad` (same contracts and invariants); `fit(s, n)` cuts or pads `s` to `n` characters
  (`fixStr`); `fmtRecordInitial` returns a string (its value is never displayed).
-/
import Examples.CardDemo.Cbcus01cProg
import Examples.CardDemo.Cbact02cHelpers

open Jimple

namespace Examples.CardDemo

abbrev cuSpacesRef : MethodRef := CU.Cbcus01c.«spaces(int)».ref
abbrev cuFmtNumRef : MethodRef := CU.Cbcus01c.«fmtNum(long,int)».ref
abbrev cuFitRef : MethodRef := CU.Cbcus01c.«fit(java.lang.String,int)».ref
abbrev cuFmtRecordInitialRef : MethodRef := CU.Cbcus01c.«fmtRecordInitial()».ref

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_spaces_vc : MethodVC CU.prog (fun _ => none) 0 cuSpacesRef spacesSpec spacesInv 60 := by
  jverify [ite_nat_ne, spacesSpec, spacesInv, Grows, fixStr]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtNum_vc : MethodVC CU.prog (fun _ => none) 0 cuFmtNumRef zeroPadSpec zeroPadInv 80 := by
  jverify [ite_nat_ne, zeroPadSpec, zeroPadInv, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char, drop_set_self]

def fitSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- After the loop's length call (statement 11): the builder holds the text padded to its length
    `k` (local `$i1`). Locals: `i0` 0, `$i1` 1, `$r1` 2, `$r0` 3. -/
def fitInv : Invariants := [(11, fun args σ0 fr σ => ∀ sv n, args = [sv, .int n] →
  ∃ sb sr k, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int k) ∧ fr.get 2 = some (.ref sb) ∧
    fr.get 3 = some (.ref sr) ∧ σ.heap sr = some (.str (argText σ0 sv)) ∧
    (argText σ0 sv).length < n.toInt.toNat ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr (argText σ0 sv) k.toInt.toNat)) ∧
    0 ≤ k.toInt ∧ (argText σ0 sv).length ≤ k.toInt.toNat ∧ k.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem cu_fit_vc : MethodVC CU.prog (fun _ => none) 0 cuFitRef fitSpec fitInv 60 := by
  jverify [ite_nat_ne, fitSpec, fitInv, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

def cuFmtNumSig : MethodSig :=
  ⟨"Cbcus01c", .cls "java.lang.String", "fmtNum", [.prim .long, .prim .int]⟩
def cuSpacesSig : MethodSig := ⟨"Cbcus01c", .cls "java.lang.String", "spaces", [.prim .int]⟩
def cuFitSig : MethodSig :=
  ⟨"Cbcus01c", .cls "java.lang.String", "fit", [.cls "java.lang.String", .prim .int]⟩

/-- `fmtRecordInitial` returns a string. -/
def fmtRecordInitialSpec : Spec := Spec.of
  (fun args σ => args = [] ∧ σ.initOf "Cbcus01c" = .done)
  (fun _ σ r σ' => ∃ x s, r = some (.ref x) ∧ σ'.heap x = some (.str s) ∧ Grows σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def friCallees : Contracts := [(cuFmtNumSig, zeroPadSpec), (cuSpacesSig, spacesSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtRecordInitial_vc :
    MethodVC CU.prog friCallees.env 0 cuFmtRecordInitialRef fmtRecordInitialSpec [] 60 := by
  jverify [ite_nat_ne, fmtRecordInitialSpec, friCallees, cuFmtNumSig, cuSpacesSig, Grows]

end Examples.CardDemo

#print axioms Examples.CardDemo.cu_spaces_vc
#print axioms Examples.CardDemo.cu_fmtNum_vc
#print axioms Examples.CardDemo.cu_fit_vc
#print axioms Examples.CardDemo.cu_fmtRecordInitial_vc
