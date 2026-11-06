/-
  Examples/CardDemo/Cbcus01cLink.lean

  The link step for CBCUS01C: each method was verified against the contracts of its callees;
  the contracts are instantiated bottom-up into `cu_run_sat`.
-/
import Examples.CardDemo.Cbcus01cRunVC

open Jimple

namespace Examples.CardDemo

theorem cu_fmtNum_sat : Sat CU.prog cuFmtNumRef zeroPadSpec := cu_fmtNum_vc.sat
theorem cu_spaces_sat : Sat CU.prog cuSpacesRef spacesSpec := cu_spaces_vc.sat
theorem cu_fit_sat : Sat CU.prog cuFitRef fitSpec := cu_fit_vc.sat

theorem cu_fmtNum_ok : ContractOK CU.prog cuFmtNumSig zeroPadSpec := by jcontract_ok [cu_fmtNum_sat]
theorem cu_spaces_ok : ContractOK CU.prog cuSpacesSig spacesSpec := by jcontract_ok [cu_spaces_sat]
theorem cu_fit_ok : ContractOK CU.prog cuFitSig fitSpec := by jcontract_ok [cu_fit_sat]

theorem cu_fmtRecordInitial_sat :
    Sat CU.prog cuFmtRecordInitialRef fmtRecordInitialSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [friCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtNum_ok
    · exact cu_spaces_ok)) cu_fmtRecordInitial_vc

theorem cu_fmtRecord_sat : Sat CU.prog cuFmtRecordRef fmtRecordSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [frCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtNum_ok
    · exact cu_fit_ok)) cu_fmtRecord_vc

theorem cu_fmtRecordInitial_ok : ContractOK CU.prog cuFmtRecordInitialSig fmtRecordInitialSpec := by
  jcontract_ok [cu_fmtRecordInitial_sat]
theorem cu_fmtRecord_ok : ContractOK CU.prog cuFmtRecordSig fmtRecordSpec := by
  jcontract_ok [cu_fmtRecord_sat]

/-- **CBCUS01C, Java side**: the contract of `Cbcus01c.run` holds in the program. -/
theorem cu_run_sat : Sat CU.prog cuRunRef cuRunSpecJ :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [cuRunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtRecordInitial_ok
    · exact cu_fmtRecord_ok)) cu_run_vc

end Examples.CardDemo

#print axioms Examples.CardDemo.cu_run_sat
