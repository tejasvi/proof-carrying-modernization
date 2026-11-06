-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermRunEntryP.lean (sha256 610942af8761b5b9...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunEntryP
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `RunEntryP`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs TransactFileAt XrefFileAt TrantypeFileAt TrancatgFileAt
  DateParmsFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tentry_p (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs)
    (args : List Value) (σ0 : State) (hpre : (runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).pre args σ0) (d : Rec) (rest : Recs) (h5 : vals5 = d :: rest)
    (et5 : JType) (es5 : List Value) (e5 : Addr) (fs5 : List (FieldKey × Value))
    (ha5 : σ0.heap a5 = some (.array et5 es5)) (hl5 : 0 < es5.length) (hle5 : es5.length < 2147483648)
    (he5 : es5[0]'hl5 = .ref e5)
    (hpe : σ0.heap e5 = some (.plain "Cbtrn03c$WsDateparmRecord" fs5))
    (hsd : SFld σ0 "Cbtrn03c$WsDateparmRecord" fs5 "wsStartDate" (Model.dStart d))
    (hed : SFld σ0 "Cbtrn03c$WsDateparmRecord" fs5 "wsEndDate" (Model.dEnd d))
    (hdl : (Model.dStart d).length = 10) (hel : (Model.dEnd d).length = 10) :
    runThinWP0 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 args σ0 := by

  jvc [runThinWP0, runSpecG, runInv, runCallees, RunAt, RunAtR, RunAt34, RunAt52, RunAt53, RunAt56, RunFiles, RunInits,
    ResAt, spacesSig, blankTranSig, compareEbcdicSig, processDetailSig, processEndSig, spacesSpecT,
    blankTranSpecT, compareEbcdicSpecC, WsRel, TranFields, SFld, LFld, StOk, Agree, StrMono,
    KeepsNonWsU, jline, wsC, fdC, resC, tranC, txtLit, jstrLit, jline_cps, map_cps,
    Native.valueOfArg, JType.isRef, StrsAt_append2, ite_nat_ne, BitVec.toInt_ofInt,
    toInt_ofInt64_small, Model.dsp, Model.out, sEntry, dOf_cons, dOf_nil, d0, argText, ebcBytes_cp037,
    cp037Str_take, cp037Str_length, ordI, Model.tDate, cp037Str_inj, xAcct_xref0, runVs, runOuter]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
