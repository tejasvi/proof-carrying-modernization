import EquivLean.Modernize.Cbtrn03c.JavaW.Pad

/-!
# CBTRN03C → Java: the contract of `spaces` holds
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

def spacesSig : MethodSig := ⟨"Cbtrn03c", .cls "java.lang.String", "spaces", [.prim .int]⟩

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [spacesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact repeat_ok)) spaces_vc

set_option maxHeartbeats 0 in
theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpec := by
  jcontract_ok [spaces_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.spaces_ok
