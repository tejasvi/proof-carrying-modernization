import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue2
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, end of file, the record area after the date range: the end
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs TransactFileAt XrefFileAt TrantypeFileAt TrancatgFileAt
  DateParmsFileAt

attribute [-jsimp] List.take_succ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_eof_hi (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i z : I32) (s : Model.St) (tv : Rec)
    (h : RunAt a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i z s tv) (hini : RunInits σ0) (hz : z = 0) (hi : vals1.length ≤ i.toInt)
    (et : JType) (es : List Value) (ha1 : σ.heap a1 = some (.array et es))
    (hlen : es.length = vals1.length) (hlen31 : vals1.length < 2147483648)
    (hpl : (Model.strOf (tv.getD 12 default)).length = 26) (htdl : (Model.tDate tv).length = 10)
    (hdl : (Model.dStart (dOf vals5)).length = 10) (hel' : (Model.dEnd (dOf vals5)).length = 10)
    (hlo : Model.cmpB (Model.tDate tv) (Model.dStart (dOf vals5)) ≠ .lt)
    (hhi : Model.cmpB (Model.tDate tv) (Model.dEnd (dOf vals5)) = .gt)
    (hrun : RunIs vals1 vals2 vals3 vals4 vals5 s false) :
    runWP a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 35 fr σ := by
  jvc [runWP, runSpecG, runInv, runCallees, RunAt, RunAtR, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    ResAt, spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig, spacesSpecT,
    blankTranSpecT, compareEbcdicSpecC, WsRel, TranFields, SFld, LFld, StOk, Agree, StrMono,
    KeepsNonWsU, jline, wsC, fdC, resC, tranC, txtLit, jstrLit, jline_cps, map_cps,
    Native.valueOfArg, JType.isRef, StrsAt_append2, ite_nat_ne, BitVec.toInt_ofInt,
    toInt_ofInt64_small, Model.dsp, Model.out, sEntry, dOf_cons, dOf_nil, d0, argText, ebcBytes_cp037,
    cp037Str_take, cp037Str_length, ordI, take10_procTs, cp037Str_inj, xAcct_xref0]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_eof_hi
