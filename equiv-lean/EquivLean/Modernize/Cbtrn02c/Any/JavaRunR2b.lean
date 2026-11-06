import EquivLean.Modernize.Cbtrn02c.Any.JavaRunR2

/-!
# CBTRN02C → Java: assigning cross-reference and account records
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev assignXrefRef : MethodRef :=
  Gen.Cbtrn02c.«assignXref(Cbtrn02c$CardXrefRecord,Cbtrn02c$CardXrefRecord)».ref

def assignXrefSpec : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$CardXrefRecord" fsd) ∧
     σ.heap s = some (.plain "Cbtrn02c$CardXrefRecord" fss) ∧
     (∀ k ∈ xrKeys, (Fields.get fsd k).isSome) ∧ (∀ k ∈ xrKeys, (Fields.get fss k).isSome))
  (fun args σ r σ' => ∀ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] →
     σ.heap d = some (.plain "Cbtrn02c$CardXrefRecord" fsd) →
     σ.heap s = some (.plain "Cbtrn02c$CardXrefRecord" fss) →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$CardXrefRecord" fs') ∧
       ∀ k ∈ xrKeys, Fields.get fs' k = Fields.get fss k)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignXref_vc : MethodVC Gen.prog (fun _ => none) 0 assignXrefRef assignXrefSpec [] 40 := by
  jverify [assignXrefSpec, xrKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]
  all_goals first
    | (simp only [setObj_setObj]
       exact ⟨_, rfl, by simp [Fields.get_set]⟩)

abbrev assignAccountRef : MethodRef :=
  Gen.Cbtrn02c.«assignAccount(Cbtrn02c$AccountRecord,Cbtrn02c$AccountRecord)».ref

def assignAccountSpec : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$AccountRecord" fsd) ∧
     σ.heap s = some (.plain "Cbtrn02c$AccountRecord" fss) ∧
     (∀ k ∈ acKeys, (Fields.get fsd k).isSome) ∧ (∀ k ∈ acKeys, (Fields.get fss k).isSome))
  (fun args σ r σ' => ∀ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] →
     σ.heap d = some (.plain "Cbtrn02c$AccountRecord" fsd) →
     σ.heap s = some (.plain "Cbtrn02c$AccountRecord" fss) →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$AccountRecord" fs') ∧
       ∀ k ∈ acKeys, Fields.get fs' k = Fields.get fss k)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignAccount_vc : MethodVC Gen.prog (fun _ => none) 0 assignAccountRef assignAccountSpec [] 40 := by
  jverify [assignAccountSpec, acKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]
  all_goals first
    | (simp only [setObj_setObj]
       exact ⟨_, rfl, by simp [Fields.get_set]⟩)

end EquivLean.Modernize.Cbtrn02c.Java
