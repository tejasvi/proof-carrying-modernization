import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, from the cut at 34 to the loop head
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields ResAt TransactFileAt XrefFileAt
  TrantypeFileAt TrancatgFileAt DateParmsFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_34 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (z : I32)
    (h : RunAt34 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr z) (htv : TranRecord.Valid Model.tran0)
    (hz0 : z = 0 → vals5 ≠ [] ∧
      fin (Model.loop vals2 vals3 vals4 (dOf vals5) vals1 Model.tran0 (sEntry vals5)) =
        Model.run vals1 vals2 vals3 vals4 vals5)
    (hz1 : z ≠ 0 → RunIs vals1 vals2 vals3 vals4 vals5 (sEntry vals5) false) :
    runWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 34 fr σ := by
  jvc [runWP, runSpecG, runInv, runCallees, RunAt, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig,
    processDetailSpecM, processEndSpecM]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_34
