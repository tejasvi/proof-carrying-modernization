import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, after findXref (19), no cross-reference: the abend
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_19n (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (pdS1c s t))
    (hi8 : fr.get 8 = some (.int (BitVec.ofInt 32 (xrefIdx xs (Model.tCard t)))))
    (hneg : xrefIdx xs (Model.tCard t) = -1)
    (htr : Model.tranStep xs ys cs d s t =
      .error (Model.abend23 (pdS1c s t) (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard t)))) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 19 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, map_cps]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_19n
