-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cLink.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cLink.lean

  The link step for CBACT02C: each method was verified against the contracts of its callees
  (`fix`, `zeroPad`, `spaces` without any); the contracts are instantiated bottom-up into
  `run_sat`, the contract of the entry point in the whole program.
-/
import EquivLean.Modernize.JL.Cbact02cRunVC

open Jimple

namespace EquivLean.Modernize.JL

theorem fix_sat : Sat EquivLean.Modernize.Cbact02c.Java.Gen.prog fixRef fixSpec := fix_vc.sat
theorem zeroPad_sat : Sat EquivLean.Modernize.Cbact02c.Java.Gen.prog zeroPadRef zeroPadSpec := zeroPad_vc.sat
theorem spaces_sat : Sat EquivLean.Modernize.Cbact02c.Java.Gen.prog spacesRef spacesSpec := spaces_vc.sat

theorem fix_ok : ContractOK EquivLean.Modernize.Cbact02c.Java.Gen.prog fixSig fixSpec := by jcontract_ok [fix_sat]
theorem zeroPad_ok : ContractOK EquivLean.Modernize.Cbact02c.Java.Gen.prog zeroPadSig zeroPadSpec := by jcontract_ok [zeroPad_sat]
theorem spaces_ok : ContractOK EquivLean.Modernize.Cbact02c.Java.Gen.prog spacesSig spacesSpec := by jcontract_ok [spaces_sat]

theorem formatCard_sat : Sat EquivLean.Modernize.Cbact02c.Java.Gen.prog formatCardRef formatCardSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [fcCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact fix_ok
    · exact zeroPad_ok)) formatCard_vc

theorem formatCard_ok : ContractOK EquivLean.Modernize.Cbact02c.Java.Gen.prog formatCardSig formatCardSpec := by
  jcontract_ok [formatCard_sat]

/-- **CBACT02C, Java side**: the contract of `Cbact02c.run` holds in the program. -/
theorem run_sat : Sat EquivLean.Modernize.Cbact02c.Java.Gen.prog runRef runSpecJ :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [runCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact formatCard_ok
    · exact spaces_ok)) run_vc

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.formatCard_sat
#print axioms EquivLean.Modernize.JL.run_sat
