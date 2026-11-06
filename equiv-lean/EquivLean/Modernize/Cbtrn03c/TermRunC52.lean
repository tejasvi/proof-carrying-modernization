-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermRunC52.lean (sha256 39741c60474ca8c2...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunC52
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `RunC52`

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
theorem run_tc52 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St) (t : Rec)
    (h : RunAt52 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s t) (hini : RunInits σ0) (hdv : WsDateparmRecord.Valid (dOf vals5))
    (hxv : ∀ v ∈ vals2, CardXrefRecord.Valid v) (hyv : ∀ v ∈ vals3, TranTypeRecord.Valid v)
    (hcv : ∀ v ∈ vals4, TranCatRecord.Valid v) :
    runThinWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 52 fr σ := by

  jvc [runThinWP, runSpecG, runInv, runCallees, RunAt, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig,
    processDetailSpecM, processEndSpecM, runVs, runOuter]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
