import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, the call of processDetail (52, to the cut at 53)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields ResAt TransactFileAt XrefFileAt
  TrantypeFileAt TrancatgFileAt DateParmsFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_c52 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St) (t : Rec)
    (h : RunAt52 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s t) (hini : RunInits σ0) (hdv : WsDateparmRecord.Valid (dOf vals5))
    (hxv : ∀ v ∈ vals2, CardXrefRecord.Valid v) (hyv : ∀ v ∈ vals3, TranTypeRecord.Valid v)
    (hcv : ∀ v ∈ vals4, TranCatRecord.Valid v) :
    runWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 52 fr σ := by
  jvc [runWP, runSpecG, runInv, runCallees, RunAt, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig,
    processDetailSpecM, processEndSpecM]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_c52
