import EquivLean.Modernize.Cbtrn03c.JavaTop.PdGlue

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contracts of the keyed lookups `findXref`, `findTranType`, `findTranCat`

cir-repin's searches (`T3/Find2.lean`): the records of the array as a membership fact, the result
in loop order (`findFrom` over the key texts of the array's elements).  Then the model's indices
(`xrefIdx`, `typeIdx`, `catIdx`): the elements are the records of the file (`XrefFileAt`, …), their
key texts the CP037 texts of the model's keys, and CP037 is injective.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-- The text of string field `f` (of class `cls`) of the record object `e` (`""` otherwise). -/
def fieldStr (σ : State) (cls : ClassName) (f : String) (e : Value) : JStr :=
  match e with
  | .ref x => match σ.heap x with
    | some (.plain _ fs) => match Fields.get fs (cls, f) with
      | some v => argText σ v
      | none => []
    | _ => []
  | _ => []

/-- The record object `v` of class `cls` has a string in field `f`. -/
def StrFieldOk (σ : State) (cls : ClassName) (f : String) (v : Value) : Prop :=
  ∃ x fs z s, v = .ref x ∧ σ.heap x = some (.plain cls fs) ∧ Fields.get fs (cls, f) = some (.ref z) ∧
    σ.heap z = some (.str s)

/-- The index of the first key `k` in `ks` at or after `i`, or -1. -/
def findFrom {α : Type} [DecidableEq α] [Inhabited α] (ks : List α) (k : α) (i : Nat) : Int :=
  if h : i < ks.length then (if ks[i] = k then i else findFrom ks k (i + 1)) else -1
termination_by ks.length - i
decreasing_by omega

theorem findFrom_ne {α : Type} [DecidableEq α] [Inhabited α] {ks : List α} {k : α} {i : Nat}
    (h : i < ks.length) (hne : ¬ k = ks.getD i default) :
    findFrom ks k i = findFrom ks k (i + 1) := by
  rw [findFrom]
  simp only [h, dite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some] at hne
  simp [Ne.symm hne]

theorem findFrom_ne' {α : Type} [DecidableEq α] [Inhabited α] {ks : List α} {k : α} {i : Nat}
    (h : i < ks.length) (hne : ¬ ks.getD i default = k) :
    findFrom ks k i = findFrom ks k (i + 1) :=
  findFrom_ne h (fun e => hne e.symm)

theorem findFrom_eq {α : Type} [DecidableEq α] [Inhabited α] {ks : List α} {k : α} {i : Nat}
    (h : i < ks.length) (he : ks.getD i default = k) : findFrom ks k i = i := by
  rw [findFrom]
  simp only [h, dite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some] at he
  simp [he]

theorem findFrom_ge {α : Type} [DecidableEq α] [Inhabited α] {ks : List α} {k : α} {i : Nat}
    (h : ks.length ≤ i) : findFrom ks k i = -1 := by
  rw [findFrom]; simp [Nat.not_lt.mpr h]

theorem ofInt_toNat_toInt (i : I32) (h0 : 0 ≤ i.toInt) : BitVec.ofInt 32 (i.toInt.toNat : Int) = i := by
  rw [Int.toNat_of_nonneg h0, BitVec.ofInt_toInt]

theorem ofInt_toNat_toInt' (i : I32) (h0 : 0 ≤ i.toInt) :
    BitVec.ofInt 32 (((i.toInt.toNat : Nat) : Int)) = i := ofInt_toNat_toInt i h0

/-! ## `findXref` -/

def xrefCls : ClassName := "Cbtrn03c$CardXrefRecord"

abbrev findXrefRef : MethodRef :=
  Gen.Cbtrn03c.«findXref(Cbtrn03c$CardXrefRecord[],java.lang.String)».ref

def findXrefSpec : Spec := Spec.of
  (fun args σ => ∃ (a y : Addr) (k : JStr) (et : JType) (xs : List Value),
     args = [.ref a, .ref y] ∧ σ.heap y = some (.str k) ∧ σ.heap a = some (.array et xs) ∧
     xs.length < 2147483648 ∧ ∀ v ∈ xs, StrFieldOk σ xrefCls "xrefCardNum" v)
  (fun args σ r σ' => ∀ (a y : Addr) (k : JStr) (et : JType) (xs : List Value),
     args = [.ref a, .ref y] → σ.heap y = some (.str k) → σ.heap a = some (.array et xs) →
     r = some (.int (BitVec.ofInt 32 (findFrom (xs.map (fieldStr σ xrefCls "xrefCardNum")) k 0))) ∧
     σ' = σ)

/-- At the loop head (statement 3): the search continues at `i`.  Locals: `i1` 2, `r1` 3,
`r0` 5. -/
def findXrefInv : Invariants := [(3, fun args σ0 fr σ => ∀ (a y : Addr) (k : JStr) (et : JType)
  (xs : List Value), args = [.ref a, .ref y] → σ0.heap y = some (.str k) →
  σ0.heap a = some (.array et xs) →
  ∃ i, fr.get 2 = some (.int i) ∧ fr.get 5 = some (.ref a) ∧ fr.get 3 = some (.ref y) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    findFrom (xs.map (fieldStr σ0 xrefCls "xrefCardNum")) k 0 =
      findFrom (xs.map (fieldStr σ0 xrefCls "xrefCardNum")) k i.toInt.toNat ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findXref_vc :
    MethodVC Gen.prog (fun _ => none) 0 findXrefRef findXrefSpec findXrefInv 40 := by
  jverify [findXrefSpec, findXrefInv, StrFieldOk, xrefCls, fieldStr, argText, findFrom_ne,
    findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD,
    List.getElem?_map]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)

/-! ## `findTranType` -/

def typeCls : ClassName := "Cbtrn03c$TranTypeRecord"

abbrev findTranTypeRef : MethodRef :=
  Gen.Cbtrn03c.«findTranType(Cbtrn03c$TranTypeRecord[],java.lang.String)».ref

def findTranTypeSpec : Spec := Spec.of
  (fun args σ => ∃ (a y : Addr) (k : JStr) (et : JType) (xs : List Value),
     args = [.ref a, .ref y] ∧ σ.heap y = some (.str k) ∧ σ.heap a = some (.array et xs) ∧
     xs.length < 2147483648 ∧ ∀ v ∈ xs, StrFieldOk σ typeCls "tranType" v)
  (fun args σ r σ' => ∀ (a y : Addr) (k : JStr) (et : JType) (xs : List Value),
     args = [.ref a, .ref y] → σ.heap y = some (.str k) → σ.heap a = some (.array et xs) →
     r = some (.int (BitVec.ofInt 32 (findFrom (xs.map (fieldStr σ typeCls "tranType")) k 0))) ∧
     σ' = σ)

/-- At the loop head (statement 3): the search continues at `i`.  Locals: `i1` 1, `r1` 3,
`r0` 5. -/
def findTranTypeInv : Invariants := [(3, fun args σ0 fr σ => ∀ (a y : Addr) (k : JStr) (et : JType)
  (xs : List Value), args = [.ref a, .ref y] → σ0.heap y = some (.str k) →
  σ0.heap a = some (.array et xs) →
  ∃ i, fr.get 1 = some (.int i) ∧ fr.get 5 = some (.ref a) ∧ fr.get 3 = some (.ref y) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    findFrom (xs.map (fieldStr σ0 typeCls "tranType")) k 0 =
      findFrom (xs.map (fieldStr σ0 typeCls "tranType")) k i.toInt.toNat ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTranType_vc :
    MethodVC Gen.prog (fun _ => none) 0 findTranTypeRef findTranTypeSpec findTranTypeInv 40 := by
  jverify [findTranTypeSpec, findTranTypeInv, StrFieldOk, typeCls, fieldStr, argText, findFrom_ne,
    findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD,
    List.getElem?_map]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)

/-! ## `findTranCat` -/

def catCls : ClassName := "Cbtrn03c$TranCatRecord"

/-- The value of `long` field `f` (of class `cls`) of the record object `e` (0 otherwise). -/
def fieldLongV (σ : State) (cls : ClassName) (f : String) (e : Value) : I64 :=
  match e with
  | .ref x => match σ.heap x with
    | some (.plain _ fs) => match Fields.get fs (cls, f) with
      | some (.long l) => l
      | _ => 0
    | _ => 0
  | _ => 0

/-- A category record object: a string type code and a `long` category code. -/
def CatOk (σ : State) (v : Value) : Prop :=
  ∃ x fs z s l, v = .ref x ∧ σ.heap x = some (.plain catCls fs) ∧
    Fields.get fs (catCls, "tranTypeCd") = some (.ref z) ∧ σ.heap z = some (.str s) ∧
    Fields.get fs (catCls, "tranCatCd") = some (.long l)

/-- The key of a category record: its type code text and category code. -/
def catKey (σ : State) (v : Value) : JStr × I64 :=
  (fieldStr σ catCls "tranTypeCd" v, fieldLongV σ catCls "tranCatCd" v)

abbrev findTranCatRef : MethodRef :=
  Gen.Cbtrn03c.«findTranCat(Cbtrn03c$TranCatRecord[],java.lang.String,long)».ref

def findTranCatSpec : Spec := Spec.of
  (fun args σ => ∃ (a y : Addr) (k : JStr) (l : I64) (et : JType) (xs : List Value),
     args = [.ref a, .ref y, .long l] ∧ σ.heap y = some (.str k) ∧
     σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧ ∀ v ∈ xs, CatOk σ v)
  (fun args σ r σ' => ∀ (a y : Addr) (k : JStr) (l : I64) (et : JType) (xs : List Value),
     args = [.ref a, .ref y, .long l] → σ.heap y = some (.str k) →
     σ.heap a = some (.array et xs) →
     r = some (.int (BitVec.ofInt 32 (findFrom (xs.map (catKey σ)) (k, l) 0))) ∧ σ' = σ)

/-- At the loop head (statement 4): the search continues at `i`.  Locals: `l0` 1, `r0` 3,
`i4` 6, `r1` 7. -/
def findTranCatInv : Invariants := [(4, fun args σ0 fr σ => ∀ (a y : Addr) (k : JStr) (l : I64)
  (et : JType) (xs : List Value), args = [.ref a, .ref y, .long l] →
  σ0.heap y = some (.str k) → σ0.heap a = some (.array et xs) →
  ∃ i, fr.get 6 = some (.int i) ∧ fr.get 3 = some (.ref a) ∧ fr.get 7 = some (.ref y) ∧
    fr.get 1 = some (.long l) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    findFrom (xs.map (catKey σ0)) (k, l) 0 = findFrom (xs.map (catKey σ0)) (k, l) i.toInt.toNat ∧
    σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTranCat_vc :
    MethodVC Gen.prog (fun _ => none) 0 findTranCatRef findTranCatSpec findTranCatInv 40 := by
  jverify [findTranCatSpec, findTranCatInv, CatOk, catCls, catKey, fieldStr, fieldLongV, argText,
    findFrom_ne, findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt',
    List.getD_eq_getElem?_getD, List.getElem?_map]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; intro h; subst_vars; omega));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done));
       done)
    | ((rw [findFrom_ne'] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done));
       done)
    | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
        fieldLongV, argText, strOf]; done)

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.findXref_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.findTranType_vc
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.findTranCat_vc
