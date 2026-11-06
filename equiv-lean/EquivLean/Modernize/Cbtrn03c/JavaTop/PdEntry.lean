import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, entry segment (statements 0–13, to the cuts at 14, 15, 34)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_entry (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (hpre : (pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs).pre args σ0)
    (htfI : TranFieldsI σ0 c t) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 0 (Frame.init true args) σ0 := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, pdS0, pdS1, cardOk, Model.cardStep]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_entry
