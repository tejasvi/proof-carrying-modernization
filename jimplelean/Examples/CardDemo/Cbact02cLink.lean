/-
  Examples/CardDemo/Cbact02cLink.lean

  The link step for CBACT02C: each method was verified against the contracts of its callees
  (`fix`, `zeroPad`, `spaces` without any); the contracts are instantiated bottom-up into
  `run_sat`, the contract of the entry point in the whole program.
-/
import Examples.CardDemo.Cbact02cRunVC

open Jimple

namespace Examples.CardDemo

theorem fix_sat : Sat CB.prog fixRef fixSpec := fix_vc.sat
theorem zeroPad_sat : Sat CB.prog zeroPadRef zeroPadSpec := zeroPad_vc.sat
theorem spaces_sat : Sat CB.prog spacesRef spacesSpec := spaces_vc.sat

theorem fix_ok : ContractOK CB.prog fixSig fixSpec := by jcontract_ok [fix_sat]
theorem zeroPad_ok : ContractOK CB.prog zeroPadSig zeroPadSpec := by jcontract_ok [zeroPad_sat]
theorem spaces_ok : ContractOK CB.prog spacesSig spacesSpec := by jcontract_ok [spaces_sat]

theorem formatCard_sat : Sat CB.prog formatCardRef formatCardSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [fcCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact fix_ok
    · exact zeroPad_ok)) formatCard_vc

theorem formatCard_ok : ContractOK CB.prog formatCardSig formatCardSpec := by
  jcontract_ok [formatCard_sat]

/-- **CBACT02C, Java side**: the contract of `Cbact02c.run` holds in the program. -/
theorem run_sat : Sat CB.prog runRef runSpecJ :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [runCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact formatCard_ok
    · exact spaces_ok)) run_vc

end Examples.CardDemo

#print axioms Examples.CardDemo.formatCard_sat
#print axioms Examples.CardDemo.run_sat
