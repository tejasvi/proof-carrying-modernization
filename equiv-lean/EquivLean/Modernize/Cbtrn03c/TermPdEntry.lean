-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermPdEntry.lean (sha256 02446f111b264ca8...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.PdEntry
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `PdEntry`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_entry_t (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (hpre : (pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs).pre args σ0)
    (htfI : TranFieldsI σ0 c t) :
    pdThinWP0 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 := by

  jvc [pdThinWP0, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, pdS0, pdS1, cardOk, Model.cardStep, lineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
