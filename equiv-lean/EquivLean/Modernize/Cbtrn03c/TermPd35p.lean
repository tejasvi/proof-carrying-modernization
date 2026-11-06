-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermPd35p.lean (sha256 fc5f492d67a6f998...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd35p
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `Pd35p`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_35p_t (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t))
    (i : Nat) (hidx : typeIdx ys (Model.tType t) = (i : Int)) (hi : i < 2147483647)
    (hi8 : fr.get 8 = some (.int (BitVec.ofInt 32 (typeIdx ys (Model.tType t))))) :
    pdThinWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 35 fr σ := by

  jvc [pdThinWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, lineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
