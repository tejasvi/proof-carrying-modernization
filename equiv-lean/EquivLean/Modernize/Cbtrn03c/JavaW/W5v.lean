import EquivLean.Modernize.Cbtrn03c.JavaW.W5a
import EquivLean.Modernize.Cbtrn03c.JavaW.W5b
import EquivLean.Modernize.Cbtrn03c.JavaW.W5c
import EquivLean.Modernize.Cbtrn03c.JavaW.W5d

/-!
# CBTRN03C → Java: `writeTransactionReport` from its segments; its contract on the model
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem tamt_lt {t : List EquivLean.Cobol.Rec.FVal} (ht : TranRecord.Valid t) :
    (Model.tAmt t).natAbs < 100000000000 := by
  obtain ⟨_, _, _, _, _, amt, _, _, _, _, _, _, _, _, rfl, -, -, -, -, -, -, hamt, -⟩ :=
    Glue.tran_shape ht
  exact hamt

theorem wtr_vcG (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (hd : WsDateparmRecord.Valid d)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hx : (Model.xAcct s.xref).natAbs < 100000000000) :
    MethodVC Gen.prog reportCalleesR.env 0 writeTransactionReportRef
      (wtrSpecG w ld lr c ty ca d s t y cc) (wtrInv w ld lr c ty ca d s t y cc) 100 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wtr_entry w ld lr c ty ca d s t y cc args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [wtrInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact wtr_s7 w ld lr c ty ca d s t y cc args σ0 fr σ hd hI
  · obtain ⟨hLC, hlc⟩ := lc_of_wsRel hI.1
    exact wtr_c8 w ld lr c ty ca d s t y cc args σ0 fr σ hLC hlc hI
  · exact wtr_s12 w ld lr c ty ca d s t y cc args σ0 fr σ hI
  · exact wtr_s13 w ld lr c ty ca d s t y cc args σ0 fr σ hd hI
  · have hTA : ∃ fsT, σ.heap c = some (.plain Top.tranC fsT) ∧
        Top.LFld Top.tranC fsT "tranAmt" (Model.tAmt t) := by
      obtain ⟨-, -, -, -, hT, -⟩ := hI.2
      obtain ⟨fsT, hcT, -, -, -, -, -, ha, -⟩ := hT
      exact ⟨fsT, hcT, ha⟩
    have hcw : c ≠ w := by
      obtain ⟨fsT, hcT, -⟩ := hTA
      obtain ⟨fsW, _, _, _, _, _, _, _, hw, -⟩ := hI.1
      intro e
      subst e
      rw [hw] at hcT
      simp [Top.tranC, Top.wsC] at hcT
    exact wtr_f14 w ld lr c ty ca d s t y cc args σ0 fr σ (tamt_lt ht) hx hcw hTA hI
  · exact wtr_s22 w ld lr c ty ca d s t y cc args σ0 fr σ ht hy hc hI

theorem wtr_satG (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (hd : WsDateparmRecord.Valid d)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hx : (Model.xAcct s.xref).natAbs < 100000000000) :
    Sat Gen.prog writeTransactionReportRef (wtrSpecG w ld lr c ty ca d s t y cc) :=
  MethodVC.sat_of_valid reportCalleesR_valid (wtr_vcG w ld lr c ty ca d s t y cc hd ht hy hc hx)

theorem xacct_of_wsRel {σ : State} {w ld lr : Addr} {d : List EquivLean.Cobol.Rec.FVal}
    {s : Model.St} (hR : Top.WsRel σ w ld lr d s) : (Model.xAcct s.xref).natAbs < 100000000000 := by
  obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, ⟨-, -, -, -, hx⟩⟩ := hR
  exact hx

/-- **`writeTransactionReport` performs `Model.report`** (the shared statement). -/
theorem writeTransactionReportM_sat :
    Sat Gen.prog writeTransactionReportRef Top.writeTransactionReportSpecM := by
  intro args σ o hpre hx
  obtain ⟨w0, ld0, lr0, c0, ty0, ca0, d0, s0, t0, y0, cc0, hargs0, hR0, hT0, ht0, hd0, hy0, hc0,
    hty0, hca0, hi1, hi2⟩ := hpre
  have key : ∀ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] →
      Top.WsRel σ w ld lr d s → Top.TranFields σ c t → TranRecord.Valid t →
      WsDateparmRecord.Valid d → TranTypeRecord.Valid y → TranCatRecord.Valid cc →
      σ.heap ty = some (.str (cp037Str (Model.yDesc y))) →
      σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) →
      (wtrSpecG w ld lr c ty ca d s t y cc).post args σ o :=
    fun w ld lr c ty ca d s t y cc h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      wtr_satG w ld lr c ty ca d s t y cc h5 h4 h6 h7 (xacct_of_wsRel h2) args σ o
        ⟨h1, h2, h3, h8, h9, hi1, hi2⟩ hx
  cases o with
  | normal r σ' => exact key
  | exc e σ' =>
    exact key w0 ld0 lr0 c0 ty0 ca0 d0 s0 t0 y0 cc0 hargs0 hR0 hT0 ht0 hd0 hy0 hc0 hty0 hca0
  | wrong m =>
    exact key w0 ld0 lr0 c0 ty0 ca0 d0 s0 t0 y0 cc0 hargs0 hR0 hT0 ht0 hd0 hy0 hc0 hty0 hca0

set_option maxHeartbeats 0 in
theorem writeTransactionReportM_ok :
    ContractOK Gen.prog Top.writeTransactionReportSig Top.writeTransactionReportSpecM := by
  jcontract_ok [writeTransactionReportM_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeTransactionReportM_ok
