import EquivLean.Modernize.Cbtrn01c.JavaRunCases
import EquivLean.Modernize.Cbtrn01c.JavaRunEntry
import EquivLean.Modernize.Cbtrn01c.JavaRunInit

/-!
# CBTRN01C → Java: `run` satisfies its contract, hence the generated statement

`run_vc` collects the verification conditions of `run` (entry path and the cut points 22, 29,
60, 92 of `RunDefs`); the callees are answered by their contracts `callees` (valid by
`callees_valid`) and the constructors are inlined. `run_sat` is the contract `runSpec` of
`JavaProof.lean`, and `java : Statement` follows by `statement_of_sat`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-! ## The callee contracts hold -/

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpec := spaces_vc.sat

set_option maxHeartbeats 0 in
theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpec := by
  jcontract_ok [spaces_sat]

theorem fdCallees_valid : Valid Gen.prog fdCallees.env := by
  apply Contracts.valid_of_ok
  simp only [fdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨digits_ok, signedZoned_ok⟩

theorem formatDalytran_sat : Sat Gen.prog formatDalytranRef formatDalytranSpec :=
  MethodVC.sat_of_valid fdCallees_valid formatDalytran_vc

set_option maxHeartbeats 0 in
theorem formatDalytran_ok : ContractOK Gen.prog formatDalytranSig formatDalytranSpec := by
  jcontract_ok [formatDalytran_sat]

theorem callees_valid : Valid Gen.prog callees.env := by
  apply Contracts.valid_of_ok
  simp only [callees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨spaces_ok, digits_ok, formatDalytran_ok⟩

/-! ## `run` -/

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded
(and evaluated) when they are matched against `MethodVC`. -/
attribute [local irreducible] bodyWP

theorem run_isStatic : runRef.decl.mods.isStatic = true := rfl

theorem run_vc (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    MethodVC Gen.prog callees.env 1 runRef (runSpecG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5)
      (runInv a1 a3 a5 vals1 vals3 vals5) 60 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0 hpre
  have hargs : args = runArgs a1 a2 a3 a4 a5 a6 := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have hl : ((runInv a1 a3 a5 vals1 vals3 vals5).inst (runArgs a1 a2 a3 a4 a5 a6) σ0).lookup 0 =
        none := rfl
    have h := run_seg0 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 hpre
    unfold RunWP at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · have h := run_seg22 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hJ
      unfold RunWP at h
      exact h
    · have h := run_seg29 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg60 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg92 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h

/-- `run` against the contract with fixed ghost values. -/
theorem run_satG (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    Sat Gen.prog runRef (runSpecG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5) :=
  MethodVC.sat_of_valid callees_valid (run_vc a1 a2 a3 a4 a5 a6 vals1 vals3 vals5)

/-- **`run` displays the lines of `Model.displayText`**: the contract `runSpec`. -/
theorem run_sat : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hm
  obtain ⟨a1, a2, a3, a4, a5, a6, vals1, vals3, vals5, rfl, h1, h3, h5, hv1, hv3, hv5, i1, i2, i3,
    i4, i5, i6, i7, i8⟩ := hpre
  have hinits : Inits σ := ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  have h0 := run_satG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 _ σ o
    ⟨rfl, ⟨h1, h3, h5, hv1, hv3, hv5⟩, hinits⟩ hm
  cases o with
  | normal r σ' =>
    intro a1' a2' a3' a4' a5' a6' vals1' vals3' vals5' hargs h1' h3' h5' hv1' hv3' hv5'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact run_satG a1 a2 a3 a4 a5 a6 vals1' vals3' vals5' _ σ _
      ⟨rfl, ⟨h1', h3', h5', hv1', hv3', hv5'⟩, hinits⟩ hm
  | exc e σ' => exact h0
  | wrong msg => exact h0

/-- **CBTRN01C → Java, every input**: the generated statement. -/
theorem java : Statement := statement_of_sat run_sat

end EquivLean.Modernize.Cbtrn01c.Java

#print axioms EquivLean.Modernize.Cbtrn01c.Java.run_sat
#print axioms EquivLean.Modernize.Cbtrn01c.Java.java
