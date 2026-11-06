import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, after findTranCat (49), both records found: their descriptions, to writeTransactionReport (66)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] KeepsNonWs XrefFileAt TrantypeFileAt TrancatgFileAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pd_49p (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hC : PdC w c a2 a3 a4 t xs ys cs σ0 fr σ) (hW : WsRel σ w ld lr d (cardOk xs s t))
    (htr : Model.tranStep xs ys cs d s t =
      .ok (Model.report d (cardOk xs s t) t (tyOf ys t) (caOf cs t)))
    (htyv : TranTypeRecord.Valid (tyOf ys t)) (hcav : TranCatRecord.Valid (caOf cs t))
    (i j : Nat) (hi : i < 2147483647) (hj : j < 2147483647)
    (hi8 : fr.get 8 = some (.int (BitVec.ofInt 32 (i : Int))))
    (hi9 : fr.get 9 = some (.int (BitVec.ofInt 32 (j : Int))))
    (et3 : JType) (es3 : List Value) (e3 : Addr) (fs3 : List (FieldKey × Value))
    (ha3 : σ.heap a3 = some (.array et3 es3)) (hil : i < es3.length) (hel3 : es3[i]'hil = .ref e3)
    (h32i : (BitVec.ofInt 32 (i : Int)).toNat = i)
    (he3 : σ.heap e3 = some (.plain "Cbtrn03c$TranTypeRecord" fs3))
    (hty : SFld σ "Cbtrn03c$TranTypeRecord" fs3 "tranTypeDesc" (Model.yDesc (tyOf ys t)))
    (et4 : JType) (es4 : List Value) (e4 : Addr) (fs4 : List (FieldKey × Value))
    (ha4 : σ.heap a4 = some (.array et4 es4)) (hjl : j < es4.length) (hel4 : es4[j]'hjl = .ref e4)
    (h32j : (BitVec.ofInt 32 (j : Int)).toNat = j)
    (he4 : σ.heap e4 = some (.plain "Cbtrn03c$TranCatRecord" fs4))
    (hca : SFld σ "Cbtrn03c$TranCatRecord" fs4 "tranCatTypeDesc" (Model.cDesc (caOf cs t))) :
    pdWP w ld lr c a2 a3 a4 d t s xs ys cs args σ0 49 fr σ := by
  jvc [pdWP, pdSpecG, pdInv, pdCallees, PdC, tranRecordTextSig, writeAccountTotalsSig, findXrefSig,
    ioStatusLineSig, findTranTypeSig, findTranCatSig, digitsSig, writeTransactionReportSig,
    tranRecordTextSpecT, ioStatusLineSpecT, digitsSpecT, WsRel, TranFields, SFld, LFld, StOk, Agree,
    StrMono, KeepsNonWsU, jline, wsC, fdC, tranC, txtLit, jstrLit, jline_cps, Native.valueOfArg,
    JType.isRef, StrsAt_append2, StrsAt_append3, ite_nat_ne, BitVec.toInt_ofInt, toInt_ofInt64_small,
    Model.dsp, Model.abend23, stOf, okB, cp037Str_inj, map_cps]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_49p
