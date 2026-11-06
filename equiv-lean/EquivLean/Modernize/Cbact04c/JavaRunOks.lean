import EquivLean.Modernize.Cbact04c.JavaRunRunDefs
import EquivLean.Modernize.Cbact04c.JavaRunCtorProofs
import EquivLean.Modernize.Cbact04c.JavaRunCopyProofs
import EquivLean.Modernize.Cbact04c.JavaRunCallSpecs
import EquivLean.Modernize.Cbact04c.JavaRunCtorF

/-!
# CBACT04C → Java: the callee contracts of `run` hold

Each helper's contract holds for its call targets and for every class a virtual call could
select (`ContractOK`); the table `runC` is valid.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The arithmetic and string helpers -/

theorem pow10_sat : Sat Gen.prog pow10Ref pow10Spec := MethodVC.sat pow10_vc

set_option maxHeartbeats 0 in
theorem pow10_ok : ContractOK Gen.prog pow10Sig pow10Spec := by
  jcontract_ok [pow10_sat]

theorem pow10C_valid : Valid Gen.prog truncC.env := by
  apply Contracts.valid_of_ok
  simp only [truncC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact pow10_ok

theorem trunc_sat : Sat Gen.prog truncRef truncSpec := MethodVC.sat_of_valid pow10C_valid trunc_vc

set_option maxHeartbeats 0 in
theorem trunc_ok : ContractOK Gen.prog truncSig truncSpec := by
  jcontract_ok [trunc_sat]

theorem fmtU_sat : Sat Gen.prog fmtURef fmtUSpec := MethodVC.sat_of_valid pow10C_valid fmtU_vc

set_option maxHeartbeats 0 in
theorem fmtU_ok : ContractOK Gen.prog fmtUSig fmtUSpec := by
  jcontract_ok [fmtU_sat]

theorem fmtUC_valid : Valid Gen.prog fmtZonedC.env := by
  apply Contracts.valid_of_ok
  simp only [fmtZonedC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact fmtU_ok

theorem fmtZoned_sat : Sat Gen.prog fmtZonedRef fmtZonedSpec :=
  MethodVC.sat_of_valid fmtUC_valid fmtZoned_vc

set_option maxHeartbeats 0 in
theorem fmtZoned_ok : ContractOK Gen.prog fmtZonedSig fmtZonedSpec := by
  jcontract_ok [fmtZoned_sat]

theorem displayTcbC_valid : Valid Gen.prog displayTcbC.env := by
  apply Contracts.valid_of_ok
  simp only [displayTcbC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨fmtU_ok, fmtZoned_ok⟩

theorem displayTcb_sat : Sat Gen.prog displayTcbRef displayTcbSpec :=
  MethodVC.sat_of_valid displayTcbC_valid displayTcb_vc

set_option maxHeartbeats 0 in
theorem displayTcb_ok : ContractOK Gen.prog displayTcbSig displayTcbSpec := by
  jcontract_ok [displayTcb_sat]

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpec := MethodVC.sat spaces_vc

set_option maxHeartbeats 0 in
theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpec := by
  jcontract_ok [spaces_sat]

theorem fixLen_sat : Sat Gen.prog fixLenRef fixLenSpec := MethodVC.sat fixLen_vc

set_option maxHeartbeats 0 in
theorem fixLen_ok : ContractOK Gen.prog fixLenSig fixLenSpec := by
  jcontract_ok [fixLen_sat]

set_option maxHeartbeats 0 in
theorem findAcct_ok : ContractOK Gen.prog findAcctSig findAcctSpec := by
  jcontract_ok [findAcct_sat]

set_option maxHeartbeats 0 in
theorem findDisc_ok : ContractOK Gen.prog findDiscSig findDiscSpec := by
  jcontract_ok [findDisc_sat]

/-! ## The record constructors and copies -/

theorem ctorTC_sat : Sat Gen.prog ctorTCRef ctorTCSpec := MethodVC.sat ctorTC_vc

set_option maxHeartbeats 0 in
theorem ctorTC_ok : ContractOK Gen.prog ctorTCSig ctorTCSpec := by
  jcontract_ok [ctorTC_sat]

theorem ctorXC_sat : Sat Gen.prog ctorXCRef ctorXCSpec := MethodVC.sat ctorXC_vc

set_option maxHeartbeats 0 in
theorem ctorXC_ok : ContractOK Gen.prog ctorXCSig ctorXCSpec := by
  jcontract_ok [ctorXC_sat]

theorem ctorAC_sat : Sat Gen.prog ctorACRef ctorACSpec := MethodVC.sat ctorAC_vc

set_option maxHeartbeats 0 in
theorem ctorAC_ok : ContractOK Gen.prog ctorACSig ctorACSpec := by
  jcontract_ok [ctorAC_sat]

theorem ctorDC_sat : Sat Gen.prog ctorDCRef ctorDCSpec := MethodVC.sat ctorDC_vc

set_option maxHeartbeats 0 in
theorem ctorDC_ok : ContractOK Gen.prog ctorDCSig ctorDCSpec := by
  jcontract_ok [ctorDC_sat]

theorem ctorRC_sat : Sat Gen.prog ctorRCRef ctorRCSpec := MethodVC.sat ctorRC_vc

set_option maxHeartbeats 0 in
theorem ctorRC_ok : ContractOK Gen.prog ctorRCSig ctorRCSpec := by
  jcontract_ok [ctorRC_sat]

theorem copyTcbC_valid : Valid Gen.prog copyTcbC.env := by
  apply Contracts.valid_of_ok
  simp only [copyTcbC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorTC_ok

theorem copyTcb_sat : Sat Gen.prog copyTcbRef (copySpec "Cbact04c$TranCatBalRecord" keysTC) :=
  MethodVC.sat_of_valid copyTcbC_valid copyTcb_vc

set_option maxHeartbeats 0 in
theorem copyTcb_ok : ContractOK Gen.prog copyTcbSig (copySpec "Cbact04c$TranCatBalRecord" keysTC) := by
  jcontract_ok [copyTcb_sat]

theorem copyXrefC_valid : Valid Gen.prog copyXrefC.env := by
  apply Contracts.valid_of_ok
  simp only [copyXrefC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorXC_ok

theorem copyXref_sat : Sat Gen.prog copyXrefRef (copySpec "Cbact04c$CardXrefRecord" keysXC) :=
  MethodVC.sat_of_valid copyXrefC_valid copyXref_vc

set_option maxHeartbeats 0 in
theorem copyXref_ok : ContractOK Gen.prog copyXrefSig (copySpec "Cbact04c$CardXrefRecord" keysXC) := by
  jcontract_ok [copyXref_sat]

theorem copyAcctC_valid : Valid Gen.prog copyAcctC.env := by
  apply Contracts.valid_of_ok
  simp only [copyAcctC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorAC_ok

theorem copyAcct_sat : Sat Gen.prog copyAcctRef (copySpec "Cbact04c$AccountRecord" keysAC) :=
  MethodVC.sat_of_valid copyAcctC_valid copyAcct_vc

set_option maxHeartbeats 0 in
theorem copyAcct_ok : ContractOK Gen.prog copyAcctSig (copySpec "Cbact04c$AccountRecord" keysAC) := by
  jcontract_ok [copyAcct_sat]

theorem copyDisC_valid : Valid Gen.prog copyDisC.env := by
  apply Contracts.valid_of_ok
  simp only [copyDisC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorDC_ok

theorem copyDis_sat : Sat Gen.prog copyDisRef (copySpec "Cbact04c$DisGroupRecord" keysDC) :=
  MethodVC.sat_of_valid copyDisC_valid copyDis_vc

set_option maxHeartbeats 0 in
theorem copyDis_ok : ContractOK Gen.prog copyDisSig (copySpec "Cbact04c$DisGroupRecord" keysDC) := by
  jcontract_ok [copyDis_sat]

theorem copyTranC_valid : Valid Gen.prog copyTranC.env := by
  apply Contracts.valid_of_ok
  simp only [copyTranC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorRC_ok

theorem copyTran_sat : Sat Gen.prog copyTranRef (copySpec "Cbact04c$TranRecord" keysRC) :=
  MethodVC.sat_of_valid copyTranC_valid copyTran_vc

set_option maxHeartbeats 0 in
theorem copyTran_ok : ContractOK Gen.prog copyTranSig (copySpec "Cbact04c$TranRecord" keysRC) := by
  jcontract_ok [copyTran_sat]

/-! ## The contracts as `run` uses them (`CallSpecs`) -/

theorem displayTcbF_sat : Sat Gen.prog displayTcbRef displayTcbF := displayTcbF_of_sat displayTcb_sat

set_option maxHeartbeats 0 in
theorem displayTcbF_ok : ContractOK Gen.prog displayTcbSig displayTcbF := by
  jcontract_ok [displayTcbF_sat]

theorem fixLenF_sat : Sat Gen.prog fixLenRef fixLenF := fixLenF_of_sat fixLen_sat

set_option maxHeartbeats 0 in
theorem fixLenF_ok : ContractOK Gen.prog fixLenSig fixLenF := by
  jcontract_ok [fixLenF_sat]

theorem findAcctF_sat : Sat Gen.prog findAcctRef findAcctF := findAcctF_of_sat findAcct_sat

set_option maxHeartbeats 0 in
theorem findAcctF_ok : ContractOK Gen.prog findAcctSig findAcctF := by
  jcontract_ok [findAcctF_sat]

theorem findDiscF_sat : Sat Gen.prog findDiscRef findDiscF := findDiscF_of_sat findDisc_sat

set_option maxHeartbeats 0 in
theorem findDiscF_ok : ContractOK Gen.prog findDiscSig findDiscF := by
  jcontract_ok [findDiscF_sat]

theorem copyTcbF_sat : Sat Gen.prog copyTcbRef (copyF "Cbact04c$TranCatBalRecord" keysTC) := copyF_of_sat copyTcb_sat

set_option maxHeartbeats 0 in
theorem copyTcbF_ok : ContractOK Gen.prog copyTcbSig (copyF "Cbact04c$TranCatBalRecord" keysTC) := by
  jcontract_ok [copyTcbF_sat]

theorem copyXrefF_sat : Sat Gen.prog copyXrefRef (copyF "Cbact04c$CardXrefRecord" keysXC) := copyF_of_sat copyXref_sat

set_option maxHeartbeats 0 in
theorem copyXrefF_ok : ContractOK Gen.prog copyXrefSig (copyF "Cbact04c$CardXrefRecord" keysXC) := by
  jcontract_ok [copyXrefF_sat]

theorem copyAcctF_sat : Sat Gen.prog copyAcctRef (copyF "Cbact04c$AccountRecord" keysAC) := copyF_of_sat copyAcct_sat

set_option maxHeartbeats 0 in
theorem copyAcctF_ok : ContractOK Gen.prog copyAcctSig (copyF "Cbact04c$AccountRecord" keysAC) := by
  jcontract_ok [copyAcctF_sat]

theorem copyDisF_sat : Sat Gen.prog copyDisRef (copyF "Cbact04c$DisGroupRecord" keysDC) := copyF_of_sat copyDis_sat

set_option maxHeartbeats 0 in
theorem copyDisF_ok : ContractOK Gen.prog copyDisSig (copyF "Cbact04c$DisGroupRecord" keysDC) := by
  jcontract_ok [copyDisF_sat]

theorem copyTranF_sat : Sat Gen.prog copyTranRef (copyF "Cbact04c$TranRecord" keysRC) := copyF_of_sat copyTran_sat

set_option maxHeartbeats 0 in
theorem copyTranF_ok : ContractOK Gen.prog copyTranSig (copyF "Cbact04c$TranRecord" keysRC) := by
  jcontract_ok [copyTranF_sat]

theorem ctorTCF_sat : Sat Gen.prog ctorTCRef ctorTCF := ctorTCF_of_sat ctorTC_sat

set_option maxHeartbeats 0 in
theorem ctorTCF_ok : ContractOK Gen.prog ctorTCSig ctorTCF := by
  jcontract_ok [ctorTCF_sat]

theorem ctorXCF_sat : Sat Gen.prog ctorXCRef ctorXCF := ctorXCF_of_sat ctorXC_sat

set_option maxHeartbeats 0 in
theorem ctorXCF_ok : ContractOK Gen.prog ctorXCSig ctorXCF := by
  jcontract_ok [ctorXCF_sat]

theorem ctorACF_sat : Sat Gen.prog ctorACRef ctorACF := ctorACF_of_sat ctorAC_sat

set_option maxHeartbeats 0 in
theorem ctorACF_ok : ContractOK Gen.prog ctorACSig ctorACF := by
  jcontract_ok [ctorACF_sat]

theorem ctorDCF_sat : Sat Gen.prog ctorDCRef ctorDCF := ctorDCF_of_sat ctorDC_sat

set_option maxHeartbeats 0 in
theorem ctorDCF_ok : ContractOK Gen.prog ctorDCSig ctorDCF := by
  jcontract_ok [ctorDCF_sat]

theorem ctorRCF_sat : Sat Gen.prog ctorRCRef ctorRCF := ctorRCF_of_sat ctorRC_sat

set_option maxHeartbeats 0 in
theorem ctorRCF_ok : ContractOK Gen.prog ctorRCSig ctorRCF := by
  jcontract_ok [ctorRCF_sat]

/-! ## The table of `run` -/

theorem runC_valid : Valid Gen.prog runC.env := by
  apply Contracts.valid_of_ok
  simp only [runC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨spaces_ok, fixLenF_ok, fmtU_ok, trunc_ok, displayTcbF_ok, findAcctF_ok, findDiscF_ok,
    copyTcbF_ok, copyXrefF_ok, copyAcctF_ok, copyDisF_ok, copyTranF_ok, ctorTCF_ok, ctorXCF_ok,
    ctorACF_ok, ctorDCF_ok, ctorRCF_ok⟩

end EquivLean.Modernize.Cbact04c.Java
