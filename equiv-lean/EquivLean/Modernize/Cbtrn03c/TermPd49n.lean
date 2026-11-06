-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermPd49n.lean (sha256 c4de94d552f69361...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd49n
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `Pd49n`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_49n_t (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (hi9 : fr.get 9 = some (.int (BitVec.ofInt 32 (catIdx cs (Model.tType t) (Model.tCat t)))))
    (hneg : catIdx cs (Model.tType t) (Model.tCat t) = -1) (hcat : (Model.tCat t).natAbs < 10000)
    (htr : Model.tranStep xs ys cs d s t =
      .error (Model.abend23 (cardOk xs s t)
        (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType t) ++ Model.digs 4 (Model.tCat t)))) :
    pdThinWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 49 fr σ := by

  jvc [pdThinWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, map_cps, lineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top
