/-
  Examples/CardDemo/Cbact03cProg.lean

  CardDemo's CBACT03C (card cross-reference file listing) as translated to Java: the program
  (`examples_java/cbact03c`), whose state lives in one object of class `Cbact03c$State`, and
  the helper contracts. `spaces`, `fixLen` and `zeroPad` have the bodies of CBCUS01C's `spaces`
  and `fit` and (up to the loop head, statement 9) of CBACT02C's `zeroPad`.
-/
import Examples.CardDemo.Cbcus01cHelpers

open Jimple

jimple_import "examples_java/cbact03c/jimple" as C3

namespace Examples.CardDemo

abbrev c3SpacesRef : MethodRef := C3.Cbact03c.«spaces(int)».ref
abbrev c3ZeroPadRef : MethodRef := C3.Cbact03c.«zeroPad(long,int)».ref
abbrev c3FixLenRef : MethodRef := C3.Cbact03c.«fixLen(java.lang.String,int)».ref
abbrev c3RecordTextRef : MethodRef := C3.Cbact03c.«recordText(Cbact03c$State)».ref

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_spaces_vc : MethodVC C3.prog (fun _ => none) 0 c3SpacesRef spacesSpec spacesInv 60 := by
  jverify [ite_nat_ne, spacesSpec, spacesInv, Grows, fixStr]

/-- `zeroPad`'s loop invariant at statement 9 (`l8` local 1, `i1` local 4, the array local 6). -/
def zeroPadInv9 : Invariants := [(9, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 4 = some (.int i) ∧ fr.get 1 = some (.long l) ∧ fr.get 6 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ l.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadStr v.toNat n.toInt.toNat =
      zpadStr l.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_zeroPad_vc : MethodVC C3.prog (fun _ => none) 0 c3ZeroPadRef zeroPadSpec zeroPadInv9 80 := by
  jverify [ite_nat_ne, zeroPadSpec, zeroPadInv9, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char, drop_set_self]

/-- `fit`'s contract with the result's freshness (`σ.next ≤ x`): the strings `getNext` stores in the
    state object are new objects, distinct from every object of the loop head. -/
def fixLenSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       σ.next ≤ x ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.hypHeapFacts true in
theorem c3_fixLen_vc : MethodVC C3.prog (fun _ => none) 0 c3FixLenRef fixLenSpec fitInv 60 := by
  jverify [ite_nat_ne, fixLenSpec, fitInv, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some]

def stCls : ClassName := "Cbact03c$State"

/-- Field `f` of the state object at `st`. -/
def sfieldOf (σ : State) (st : Addr) (f : String) : Value :=
  match σ.heap st with
  | some (.plain _ fs) => (Fields.get fs (stCls, f)).getD .null
  | _ => .null

def sfieldLong (σ : State) (st : Addr) (f : String) : I64 :=
  match sfieldOf σ st f with
  | .long x => x
  | _ => 0

/-- The line `recordText` builds from the record fields of the state object. -/
def stateLine (σ : State) (st : Addr) : JStr :=
  argText σ (sfieldOf σ st "recCardNum") ++ zpadStr (sfieldLong σ st "recCustId").toNat 9 ++
    zpadStr (sfieldLong σ st "recAcctId").toNat 11 ++ argText σ (sfieldOf σ st "recFiller")

/-- The record fields of the state object hold strings and non-negative numbers. -/
def StateRecOk (σ : State) (st : Addr) : Prop :=
  ∃ sfs x1 s1 a b x2 s2, σ.heap st = some (.plain stCls sfs) ∧
    Fields.get sfs (stCls, "recCardNum") = some (.ref x1) ∧ σ.heap x1 = some (.str s1) ∧
    Fields.get sfs (stCls, "recCustId") = some (.long a) ∧ 0 ≤ a.toInt ∧
    Fields.get sfs (stCls, "recAcctId") = some (.long b) ∧ 0 ≤ b.toInt ∧
    Fields.get sfs (stCls, "recFiller") = some (.ref x2) ∧ σ.heap x2 = some (.str s2)

def c3ZeroPadSig : MethodSig :=
  ⟨"Cbact03c", .cls "java.lang.String", "zeroPad", [.prim .long, .prim .int]⟩

def recordTextSpec : Spec := Spec.of
  (fun args σ => ∃ st, args = [.ref st] ∧ StateRecOk σ st ∧ σ.initOf "Cbact03c" = .done)
  (fun args σ r σ' => ∀ st, args = [.ref st] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (stateLine σ st)) ∧ σ.next ≤ x ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def rtCallees : Contracts := [(c3ZeroPadSig, zeroPadSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_recordText_vc :
    MethodVC C3.prog rtCallees.env 0 c3RecordTextRef recordTextSpec [] 60 := by
  jverify [ite_nat_ne, recordTextSpec, rtCallees, c3ZeroPadSig, StateRecOk, stateLine, sfieldOf, sfieldLong,
    argText, Grows, stCls]

end Examples.CardDemo

#print axioms Examples.CardDemo.c3_spaces_vc
#print axioms Examples.CardDemo.c3_zeroPad_vc
#print axioms Examples.CardDemo.c3_fixLen_vc
#print axioms Examples.CardDemo.c3_recordText_vc
