import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs

/-!
# CBTRN02C → Java: `writeReject` satisfies its contract
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem writeReject_sat : Sat Gen.prog writeRejectRef writeRejectSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [wrCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact dalytranText_ok
    · exact padNum_ok
    · exact reasonDesc_ok
    · exact fitF_ok)) writeReject_vc

set_option maxHeartbeats 0 in
theorem writeReject_ok : ContractOK Gen.prog writeRejectSig writeRejectSpec := by
  jcontract_ok [writeReject_sat]

end EquivLean.Modernize.Cbtrn02c.Java
