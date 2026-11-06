-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermEntry.lean (sha256 0d4c69196071b916...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRunEntry
import EquivLean.Modernize.Cbtrn01c.JavaTermDefs

/-!
# CBTRN01C → Java, termination: thin twin of `run_seg0` (`JavaRunEntry`)

The statement and the preamble of the original, the cut assertions the variants (`runVs`),
calls by `callWPT` without preconditions (`callWPThin`); variant goals by the program variant closer.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg0 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (σ0 : State)
    (hpre : runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0) :
    RunThinWP0 a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 := by

  obtain ⟨-, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ := hpre
  clear hin
  unfold RunThinWP0
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, spacesSpec, runArgs,
    inlineFuel, fields_get_cons, fields_get_nil, jstrLitT]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  all_goals cbtrn01c_variant

end EquivLean.Modernize.Cbtrn01c.Java
