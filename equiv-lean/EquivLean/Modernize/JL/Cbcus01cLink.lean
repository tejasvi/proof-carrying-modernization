-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cLink.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cLink.lean

  The link step for CBCUS01C: each method was verified against the contracts of its callees;
  the contracts are instantiated bottom-up into `cu_run_sat`.
-/
import EquivLean.Modernize.JL.Cbcus01cRunVC

open Jimple

namespace EquivLean.Modernize.JL

theorem cu_fmtNum_sat : Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtNumRef zeroPadSpec := cu_fmtNum_vc.sat
theorem cu_spaces_sat : Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuSpacesRef spacesSpec := cu_spaces_vc.sat
theorem cu_fit_sat : Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFitRef fitSpec := cu_fit_vc.sat

theorem cu_fmtNum_ok : ContractOK EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtNumSig zeroPadSpec := by jcontract_ok [cu_fmtNum_sat]
theorem cu_spaces_ok : ContractOK EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuSpacesSig spacesSpec := by jcontract_ok [cu_spaces_sat]
theorem cu_fit_ok : ContractOK EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFitSig fitSpec := by jcontract_ok [cu_fit_sat]

theorem cu_fmtRecordInitial_sat :
    Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordInitialRef fmtRecordInitialSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [friCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtNum_ok
    · exact cu_spaces_ok)) cu_fmtRecordInitial_vc

theorem cu_fmtRecord_sat : Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordRef fmtRecordSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [frCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtNum_ok
    · exact cu_fit_ok)) cu_fmtRecord_vc

theorem cu_fmtRecordInitial_ok : ContractOK EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordInitialSig fmtRecordInitialSpec := by
  jcontract_ok [cu_fmtRecordInitial_sat]
theorem cu_fmtRecord_ok : ContractOK EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuFmtRecordSig fmtRecordSpec := by
  jcontract_ok [cu_fmtRecord_sat]

/-- **CBCUS01C, Java side**: the contract of `Cbcus01c.run` holds in the program. -/
theorem cu_run_sat : Sat EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunRef cuRunSpecJ :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [cuRunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact cu_fmtRecordInitial_ok
    · exact cu_fmtRecord_ok)) cu_run_vc

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_run_sat
