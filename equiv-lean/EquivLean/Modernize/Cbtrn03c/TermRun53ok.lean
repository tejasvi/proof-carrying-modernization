-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermRun53ok.lean (sha256 a68257c023307e0b...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.Run53ok
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `Run53ok`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields ResAt TransactFileAt XrefFileAt
  TrantypeFileAt TrancatgFileAt DateParmsFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_t53ok (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St) (t : Rec)
    (h : RunAt53 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s t)
    (hok : okB (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t) = true)
    (hfin : fin (Model.loop vals2 vals3 vals4 (dOf vals5) (vals1.drop i.toInt.toNat) t
      (stOf (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t))) =
        Model.run vals1 vals2 vals3 vals4 vals5) :
    runThinWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 53 fr σ := by

  jvc [runThinWP, runSpecG, runInv, runCallees, RunAt, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig,
    processDetailSpecM, processEndSpecM, stOf, okB, runVs, runOuter]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
