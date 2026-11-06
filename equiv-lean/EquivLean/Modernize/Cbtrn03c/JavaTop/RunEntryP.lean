import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, entry with a date record (to the cut at 34)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs TransactFileAt XrefFileAt TrantypeFileAt TrancatgFileAt
  DateParmsFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_entry_p (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (hpre : (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).pre args σ0) (d : Rec) (rest : Recs) (h5 : vals5 = d :: rest)
    (et5 : JType) (es5 : List Value) (e5 : Addr) (fs5 : List (FieldKey × Value))
    (ha5 : σ0.heap a5 = some (.array et5 es5)) (hl5 : 0 < es5.length) (hle5 : es5.length < 2147483648)
    (he5 : es5[0]'hl5 = .ref e5)
    (hpe : σ0.heap e5 = some (.plain "Cbtrn03c$WsDateparmRecord" fs5))
    (hsd : SFld σ0 "Cbtrn03c$WsDateparmRecord" fs5 "wsStartDate" (Model.dStart d))
    (hed : SFld σ0 "Cbtrn03c$WsDateparmRecord" fs5 "wsEndDate" (Model.dEnd d))
    (hdl : (Model.dStart d).length = 10) (hel : (Model.dEnd d).length = 10) :
    runWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 0 (Frame.init true args) σ0 := by
  jvc [runWP, runSpecG, runInv, runCallees, RunAt, RunAtR, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    ResAt, spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig, spacesSpecT,
    blankTranSpecT, compareEbcdicSpecC, WsRel, TranFields, SFld, LFld, StOk, Agree, StrMono,
    KeepsNonWsU, jline, wsC, fdC, resC, tranC, txtLit, jstrLit, jline_cps, map_cps,
    Native.valueOfArg, JType.isRef, StrsAt_append2, ite_nat_ne, BitVec.toInt_ofInt,
    toInt_ofInt64_small, Model.dsp, Model.out, sEntry, dOf_cons, dOf_nil, d0, argText, ebcBytes_cp037,
    cp037Str_take, cp037Str_length, ordI, Model.tDate, cp037Str_inj, xAcct_xref0]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_entry_p
