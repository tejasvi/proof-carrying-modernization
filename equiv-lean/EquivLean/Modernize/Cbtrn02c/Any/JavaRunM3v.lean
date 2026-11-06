import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs

/-!
# CBTRN02C → Java: `updateAccount`'s verification conditions, and its contract
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem updateAccount_vc :
    MethodVC Gen.prog uaCallees.env 0 updateAccountRef updateAccountSpec [] 60 := by
  refine ⟨uaBody, rfl, ?_⟩
  intro args σ0 hpre
  have hpre' := hpre
  obtain ⟨r, d, wA, aD, -, -, -, -, -, -, -, -, -, -, -, -, hargs, -⟩ := hpre'
  subst hargs
  refine ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩
  have := ua_entry r d wA aD σ0 hpre
  unfold UaWP uaPost at this
  exact this

set_option maxHeartbeats 0 in
theorem findAccountF_ok' : ContractOK Gen.prog findAccountSig' findAccountSpecF := by
  jcontract_ok [findAccountF_sat]

theorem updateAccount_sat : Sat Gen.prog updateAccountRef updateAccountSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [uaCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact findAccountF_ok'
    · exact copyAccountF_ok)) updateAccount_vc

set_option maxHeartbeats 0 in
theorem updateAccount_ok : ContractOK Gen.prog updateAccountSig updateAccountSpec := by
  jcontract_ok [updateAccount_sat]

end EquivLean.Modernize.Cbtrn02c.Java
