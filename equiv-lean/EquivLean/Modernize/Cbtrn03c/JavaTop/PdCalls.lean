import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd
import EquivLean.Modernize.Cbtrn03c.JavaTop.Frames

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, the calls at cuts (statements 14, 18, 34, 48, 66)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields XrefFileAt TrantypeFileAt
  TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_c14 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (pdS0 s t))
    (hcard : (pdS0 s t).card ≠ Model.tCard t) (hfirst : (pdS0 s t).first = false) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 14 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    writeAccountTotalsSpecM, wsStepSpec, pdS1]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_c18 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (pdS1c s t))
    (hcard : (pdS0 s t).card ≠ Model.tCard t) (y : Addr) (hy : fr.get 10 = some (.ref y))
    (hys : σ.heap y = some (.str (cp037Str (Model.tCard t))))
    (hxv : ∀ v ∈ xs, CardXrefRecord.Valid v) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 18 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    findXrefSpecT]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_c34 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t)) (y : Addr)
    (hy : fr.get 10 = some (.ref y)) (hys : σ.heap y = some (.str (cp037Str (Model.tType t))))
    (hyv : ∀ v ∈ ys, TranTypeRecord.Valid v) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 34 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    findTranTypeSpecT]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_c48 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t))
    (hti : 0 ≤ typeIdx ys (Model.tType t))
    (hi8 : fr.get 8 = some (.int (BitVec.ofInt 32 (typeIdx ys (Model.tType t)))))
    (hl1 : fr.get 4 = some (.long (BitVec.ofInt 64 (Model.tCat t)))) (y : Addr)
    (hy : fr.get 10 = some (.ref y)) (hys : σ.heap y = some (.str (cp037Str (Model.tType t))))
    (hcv : ∀ v ∈ cs, TranCatRecord.Valid v) (hcat : (Model.tCat t).natAbs < 10000) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 48 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    findTranCatSpecT, BitVec.toInt_ofInt, toInt_ofInt64_small]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_c66 (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (htr : Model.tranStep xs ys cs d s t =
      .ok (Model.report d (cardOk xs s t) t (tyOf ys t) (caOf cs t)))
    (htyv : TranTypeRecord.Valid (tyOf ys t)) (hcav : TranCatRecord.Valid (caOf cs t))
    (ty ca : Addr) (hty : fr.get 10 = some (.ref ty)) (hca : fr.get 11 = some (.ref ca))
    (htys : σ.heap ty = some (.str (cp037Str (Model.yDesc (tyOf ys t)))))
    (hcas : σ.heap ca = some (.str (cp037Str (Model.cDesc (caOf cs t)))))
    (htv : TranRecord.Valid t) (hdv : WsDateparmRecord.Valid d) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 66 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    writeTransactionReportSpecM, stOf, okB]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_c14
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_c18
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_c34
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_c48
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_c66
