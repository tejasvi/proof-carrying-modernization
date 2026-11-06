import EquivLean.Demo.Thrift.Java.Gam2

/-!
# Thrift → Java (T4): method selection on `TCompactProtocol`, and contracts from proved bodies

A contract in a callee environment is valid (`ContractOK`) when every target of its signature
satisfies it and, for every application subclass, the method a virtual call selects does
(`NoRedecl`: no application subclass redeclares it).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem contains_sub {P : Program} {cs cs' : List ClassDecl} (h : Contains P cs)
    (hs : ∀ d ∈ cs', d ∈ cs) : Contains P cs' :=
  ⟨h.1, fun d hd => h.2 d (hs d hd)⟩

/-- An instance method of `TCompactProtocol` found by name and signature. -/
theorem chainN_cp {P : Program} (hF : P.findClass cpCls = some cpC) (n : Nat) {sub : SubSig}
    {m : MethodDecl} (hm : Program.ClassDecl.findMethod cpC sub false = some m) :
    P.chainN (n + 1) cpCls sub false = .jimple ⟨cpCls, m⟩ := by
  rw [Program.chainN.eq_2, hF]
  simp only [hm]

/-- No static method of that name in `TCompactProtocol` or `TProtocol`: the search ends at the
library class `java.lang.Object`. -/
theorem chainN_static_cp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none) (n : Nat)
    {sub : SubSig} (hm1 : Program.ClassDecl.findMethod cpC sub true = none)
    (hm2 : Program.ClassDecl.findMethod tpC sub true = none) :
    P.chainN (n + 1 + 1 + 1) cpCls sub true = .native "java.lang.Object" := by
  rw [Program.chainN.eq_2, hF]
  simp only [hm1]
  rw [show cpC.super = some tpCls from rfl]
  simp only []
  rw [Program.chainN.eq_2, hT]
  simp only [hm2]
  rw [show tpC.super = some "java.lang.Object" from rfl]
  simp only []
  rw [Program.chainN.eq_2, hO]
  rfl

/-- The targets of a `TCompactProtocol` instance method: the method itself. -/
theorem targets_cp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none)
    {r : JType} {name : String} {ps : List JType} {m : MethodDecl}
    (hm : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ false = some m)
    (hm1 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ true = none)
    (hm2 : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ true = none)
    (hcl : name ≠ "<clinit>") {m' : MethodRef}
    (ht : Targets P ⟨cpCls, r, name, ps⟩ m') : m' = ⟨cpCls, m⟩ := by
  obtain ⟨hsel, -⟩ := ht
  rcases hsel with hs | hs | ⟨hc, -⟩
  · simp only [Program.selectStatic, MethodSig.sub] at hs
    rw [show Program.fuel P = 4093 + 1 + 1 + 1 from rfl,
      chainN_static_cp hF hT hO 4093 hm1 hm2] at hs
    cases hs
  · simp only [Program.selectSpecial, MethodSig.sub] at hs
    rw [show Program.fuel P = 4095 + 1 from rfl, chainN_cp hF 4095 hm] at hs
    simp only [Program.Target.jimple.injEq] at hs
    exact hs.symm
  · unfold clinitSig at hc
    simp only [MethodSig.mk.injEq] at hc
    exact absurd hc.2.2.1 hcl

/-- A contract of a `TCompactProtocol` instance method, from its proved body and `NoRedecl`. -/
theorem contractOK_cp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none)
    {r : JType} {name : String} {ps : List JType} {m : MethodDecl} {S : Spec}
    (hm : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ false = some m)
    (hm1 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ true = none)
    (hm2 : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ true = none)
    (hcl : name ≠ "<clinit>") (hsat : Sat P ⟨cpCls, m⟩ S)
    (hnr : NoRedecl P ⟨cpCls, r, name, ps⟩ ⟨cpCls, m⟩) :
    ContractOK P ⟨cpCls, r, name, ps⟩ S := by
  refine ⟨fun m' ht => ?_, fun c hc hs _ => vsat_of_jimple (hnr c hc hs) hsat⟩
  rw [targets_cp hF hT hO hm hm1 hm2 hcl ht]
  exact hsat

end EquivLean.Demo.Thrift.Java
