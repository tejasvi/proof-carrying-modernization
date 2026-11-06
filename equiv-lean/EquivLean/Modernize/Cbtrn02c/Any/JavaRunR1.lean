import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: copying records

`copyTcat(t)`: a new category balance object with the fields of `t`.  `assignTcat(d, s)`: the
fields of `s` into `d`.  Stated over the field keys of the class.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The fields of `Cbtrn02c$TranCatBalRecord`. -/
def tcKeys : List FieldKey :=
  [("Cbtrn02c$TranCatBalRecord", "trancatAcctId"), ("Cbtrn02c$TranCatBalRecord", "trancatTypeCd"),
   ("Cbtrn02c$TranCatBalRecord", "trancatCd"), ("Cbtrn02c$TranCatBalRecord", "tranCatBal"),
   ("Cbtrn02c$TranCatBalRecord", "filler1")]

abbrev copyTcatRef : MethodRef := Gen.Cbtrn02c.«copyTcat(Cbtrn02c$TranCatBalRecord)».ref

def copyTcatSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧
     (∀ k ∈ tcKeys, (Fields.get fs k).isSome) ∧ σ.initOf "Cbtrn02c$TranCatBalRecord" = .done)
  (fun args σ r σ' => ∀ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] →
     σ.heap a = some (.plain "Cbtrn02c$TranCatBalRecord" fs) →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧
       σ'.heap x = some (.plain "Cbtrn02c$TranCatBalRecord" fs') ∧
       (∀ k ∈ tcKeys, Fields.get fs' k = Fields.get fs k) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyTcat_vc : MethodVC Gen.prog (fun _ => none) 1 copyTcatRef copyTcatSpec [] 40 := by
  jverify [copyTcatSpec, tcKeys, Grows, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]

abbrev assignTcatRef : MethodRef :=
  Gen.Cbtrn02c.«assignTcat(Cbtrn02c$TranCatBalRecord,Cbtrn02c$TranCatBalRecord)».ref

def assignTcatSpec : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$TranCatBalRecord" fsd) ∧
     σ.heap s = some (.plain "Cbtrn02c$TranCatBalRecord" fss) ∧
     (∀ k ∈ tcKeys, (Fields.get fsd k).isSome) ∧ (∀ k ∈ tcKeys, (Fields.get fss k).isSome))
  (fun args σ r σ' => ∀ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] →
     σ.heap d = some (.plain "Cbtrn02c$TranCatBalRecord" fsd) →
     σ.heap s = some (.plain "Cbtrn02c$TranCatBalRecord" fss) →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$TranCatBalRecord" fs') ∧
       ∀ k ∈ tcKeys, Fields.get fs' k = Fields.get fss k)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignTcat_vc : MethodVC Gen.prog (fun _ => none) 0 assignTcatRef assignTcatSpec [] 40 := by
  jverify [assignTcatSpec, tcKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]
  all_goals first
    | (simp only [setObj_setObj]
       exact ⟨_, rfl, by simp [Fields.get_set]⟩)

end EquivLean.Modernize.Cbtrn02c.Java
