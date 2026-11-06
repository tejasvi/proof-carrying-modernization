import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH6
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunL

/-!
# CBTRN02C → Java: `writeReject`

`writeReject(r, d, reason)`: a `RejectRecord` holding the text of `d` (`dtLine`) and the trailer
(the reason in 4 digits, its description fitted to 76 characters), added to
`r.dalyrejsFileWrites`.  Only that list changes; the rest of the heap grows.  The postcondition is
a function of the state at the call.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

def dalytranTextSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "java.lang.String", "dalytranText", [.cls "Cbtrn02c$DalytranRecord"]⟩
def reasonDescSig : MethodSig := ⟨"Cbtrn02c", .cls "java.lang.String", "reasonDesc", [.prim .int]⟩

theorem dalytranText_sat : Sat Gen.prog dalytranTextRef dalytranTextSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [dtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact fitF_ok
    · exact padNum_ok
    · exact zonedSigned_ok)) dalytranText_vc
set_option maxHeartbeats 0 in
theorem dalytranText_ok : ContractOK Gen.prog dalytranTextSig dalytranTextSpec := by
  jcontract_ok [dalytranText_sat]

theorem reasonDesc_sat : Sat Gen.prog reasonDescRef reasonDescSpec := reasonDesc_vc.sat
set_option maxHeartbeats 0 in
theorem reasonDesc_ok : ContractOK Gen.prog reasonDescSig reasonDescSpec := by
  jcontract_ok [reasonDesc_sat]

abbrev rejKey : FieldKey := ("Cbtrn02c$Result", "dalyrejsFileWrites")

abbrev writeRejectRef : MethodRef :=
  Gen.Cbtrn02c.«writeReject(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,int)».ref

def wrCallees : Contracts :=
  [(dalytranTextSig, dalytranTextSpec), (padNumSig, padNumSpec), (reasonDescSig, reasonDescSpec),
   (fitSig, fitSpecF)]

def writeRejectSpec : Spec := Spec.of
  (fun args σ => ∃ (r d : Addr) (k : I32) (fsR : List (FieldKey × Value)) (lR : Addr)
       (xs : List Value) (m : Nat),
     args = [.ref r, .ref d, .int k] ∧ (k = 100#32 ∨ k = 101#32 ∨ k = 102#32 ∨ k = 103#32) ∧
     σ.heap r = some (.plain "Cbtrn02c$Result" fsR) ∧ Fields.get fsR rejKey = some (.ref lR) ∧
     σ.heap lR = some (.list .arrayList xs m) ∧ Hide (DalOk σ d) ∧ σ.initOf "Cbtrn02c" = .done ∧
     σ.initOf "Cbtrn02c$RejectRecord" = .done)
  (fun args σ r' σ' => ∀ (r d : Addr) (k : I32), args = [.ref r, .ref d, .int k] →
     ∃ (y : Addr) (fsy : List (FieldKey × Value)) (t1 t2 : Addr) (m' : Nat),
       σ'.heap (refField σ r rejKey) =
         some (.list .arrayList (listOf σ (refField σ r rejKey) ++ [.ref y]) m') ∧
       σ.next ≤ y ∧ σ'.heap y = some (.plain "Cbtrn02c$RejectRecord" fsy) ∧
       Fields.get fsy ("Cbtrn02c$RejectRecord", "rejectTranData") = some (.ref t1) ∧
       σ'.heap t1 = some (.str (dtLine σ d)) ∧
       Fields.get fsy ("Cbtrn02c$RejectRecord", "validationTrailer") = some (.ref t2) ∧
       σ'.heap t2 = some (.str (trailerJ k)) ∧ FrameS σ σ' [refField σ r rejKey] ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem writeReject_vc :
    MethodVC Gen.prog wrCallees.env 1 writeRejectRef writeRejectSpec [] 60 := by
  jverify [writeRejectSpec, wrCallees, dalytranTextSig, dalytranTextSpec, padNumSig, padNumSpec,
    reasonDescSig, reasonDescSpec, fitSig, fitSpecF, Grows, FrameS, trailerJ, narrow_cls, refField,
    listOf, fieldsOf, argText, strOfV, evalDynamic, concatRecipe, Native.valueOfArg, valueOfObj_eq,
    valueOfObjN_ref, Native.nObjStr, Native.primStr, JType.isRef, jstrLitT]
  all_goals first
    | exact Hide.elim (by assumption)
    | exact ⟨_, _, _, ⟨rfl, rfl⟩, by assumption,
        by unfold descJ; split <;> (try split) <;> (try split) <;> decide, by decide, by decide⟩

end EquivLean.Modernize.Cbtrn02c.Java
