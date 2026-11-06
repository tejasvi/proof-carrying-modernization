import EquivLean.Modernize.Cbstm03a.Java.Term.Fix

/-!
# CBSTM03A → Java, termination: `app`, `para`, `star`

`app(dst, cap, src, delim)` (no loop) appends `src` (cut at `delim`) to the builder `dst`, at most up to `cap`
characters. Its frame contract (`appSpecT`): the builder stays a builder whose text is at most `max b cap` long,
no other object changes (`Keeps`); exceptions (`substring` at an `indexOf` the contract does not bound) leave an
allocated exception object. `para` and `star` (no loops) build a new builder by `app` calls (`appSpecT`) and call
`fix` (`fixSpecT`) on its text: direct termination VCs, postcondition `True`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

abbrev appRef : MethodRef := Gen.Cbstm03a.«app(java.lang.StringBuilder,int,java.lang.String,java.lang.String)».ref
abbrev paraRef : MethodRef := Gen.Cbstm03a.«para(java.lang.String,java.lang.String)».ref
abbrev starRef : MethodRef := Gen.Cbstm03a.«star(java.lang.String,java.lang.String)».ref
def appSig : MethodSig :=
  ⟨"Cbstm03a", .void, "app", [.cls "java.lang.StringBuilder", .prim .int, .cls "java.lang.String",
    .cls "java.lang.String"]⟩
def paraSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "para", [.cls "java.lang.String", .cls "java.lang.String"]⟩
def starSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "star", [.cls "java.lang.String", .cls "java.lang.String"]⟩

/-- The builder argument of `app`, its capacity, and a builder's text length. -/
def bAddr : List Value → Addr
  | .ref d :: _ => d
  | _ => 0
def capOf : List Value → Nat
  | _ :: .int c :: _ => c.toInt.toNat
  | _ => 0
def bLenAt (σ : State) (d : Addr) : Nat :=
  match σ.heap d with
  | some (.builder _ b) => b.length
  | _ => 0

def appSpecT : Spec := Spec.of
  (fun args σ => ∃ (d : Addr) (cap : I32) (sv dv : Value) (b : JStr), args = [.ref d, .int cap, sv, dv] ∧
     σ.heap d = some (.builder "java.lang.StringBuilder" b) ∧ b.length < 2147483648 ∧ 0 ≤ cap.toInt ∧
     StrArgN σ sv ∧ StrArg σ dv)
  (fun args σ _ σ' => ∃ t, σ'.heap (bAddr args) = some (.builder "java.lang.StringBuilder" t) ∧
     t.length ≤ max (bLenAt σ (bAddr args)) (capOf args) ∧ Keeps (fun y => y = bAddr args) σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)
  (fun _ σ e σ' => σ'.inits = σ.inits ∧ ∃ o, σ'.heap e = some o)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem app_vcT : MethodVC Gen.prog (fun _ => none) 0 appRef appSpecT [] 40 := by
  jverify [ite_nat_ne, findHandler, appSpecT, StrArgN, StrArg, Keeps, bAddr, capOf, bLenAt]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem app_thinT : ThinVC Gen.prog (fun _ => none) 0 appRef appSpecT [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ite_nat_ne, findHandler, appSpecT, StrArgN, StrArg, bAddr, capOf, bLenAt]

theorem app_termT : ∀ args σ, appSpecT.pre args σ → MTerm Gen.prog appRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) app_vcT app_thinT)
theorem app_satT : Sat Gen.prog appRef appSpecT := app_vcT.sat

set_option maxHeartbeats 4000000 in
theorem app_ctermT : ContractTerm Gen.prog appSig appSpecT := by jcontract_term [app_termT]
set_option maxHeartbeats 4000000 in
theorem app_okT : ContractOK Gen.prog appSig appSpecT := by jcontract_ok [app_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.app_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.app_okT
