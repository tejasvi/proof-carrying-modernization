-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact03cLink.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`C3`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact03c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact03cLink.lean

  The link step for CBACT03C: the helper contracts, then `c3_run_sat`.
-/
import EquivLean.Modernize.JL.Cbact03cRunVC

open Jimple

namespace EquivLean.Modernize.JL

theorem c3_spaces_sat : Sat EquivLean.Modernize.Cbact03c.Java.Gen.prog c3SpacesRef spacesSpec := c3_spaces_vc.sat
theorem c3_zeroPad_sat : Sat EquivLean.Modernize.Cbact03c.Java.Gen.prog c3ZeroPadRef zeroPadSpec := c3_zeroPad_vc.sat
theorem c3_fixLen_sat : Sat EquivLean.Modernize.Cbact03c.Java.Gen.prog c3FixLenRef fixLenSpec := c3_fixLen_vc.sat

theorem c3_spaces_ok : ContractOK EquivLean.Modernize.Cbact03c.Java.Gen.prog c3SpacesSig spacesSpec := by jcontract_ok [c3_spaces_sat]
theorem c3_zeroPad_ok : ContractOK EquivLean.Modernize.Cbact03c.Java.Gen.prog c3ZeroPadSig zeroPadSpec := by jcontract_ok [c3_zeroPad_sat]
theorem c3_fixLen_ok : ContractOK EquivLean.Modernize.Cbact03c.Java.Gen.prog c3FixLenSig fixLenSpec := by jcontract_ok [c3_fixLen_sat]

theorem c3_recordText_sat : Sat EquivLean.Modernize.Cbact03c.Java.Gen.prog c3RecordTextRef recordTextSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [rtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact c3_zeroPad_ok)) c3_recordText_vc

theorem c3_recordText_ok : ContractOK EquivLean.Modernize.Cbact03c.Java.Gen.prog c3RecordTextSig recordTextSpec := by
  jcontract_ok [c3_recordText_sat]

/-- **CBACT03C, Java side**: the contract of `Cbact03c.run` holds in the program. -/
theorem c3_run_sat : Sat EquivLean.Modernize.Cbact03c.Java.Gen.prog c3RunRef c3RunSpecJ :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [c3RunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact c3_spaces_ok
    · exact c3_fixLen_ok
    · exact c3_recordText_ok)) c3_run_vc

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.c3_run_sat
