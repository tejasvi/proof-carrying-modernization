-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermWThin.lean (sha256 08f19647f55ed881...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W2v
import EquivLean.Modernize.Cbtrn03c.JavaW.W3v
import EquivLean.Modernize.Cbtrn03c.JavaW.W4v
import EquivLean.Modernize.Cbtrn03c.JavaW.W5v
import EquivLean.Modernize.Cbtrn03c.TermW2a
import EquivLean.Modernize.Cbtrn03c.TermW2b
import EquivLean.Modernize.Cbtrn03c.TermW2c
import EquivLean.Modernize.Cbtrn03c.TermW3a
import EquivLean.Modernize.Cbtrn03c.TermW3b
import EquivLean.Modernize.Cbtrn03c.TermW4a
import EquivLean.Modernize.Cbtrn03c.TermW4b
import EquivLean.Modernize.Cbtrn03c.TermW4c
import EquivLean.Modernize.Cbtrn03c.TermW5a
import EquivLean.Modernize.Cbtrn03c.TermW5b
import EquivLean.Modernize.Cbtrn03c.TermW5c
import EquivLean.Modernize.Cbtrn03c.TermW5d

/-!
# CBTRN03C → Java, termination: the working-state writers' thin VCs

The thin VCs of `writePageTotals_vcG`, `writeAccountTotals_vcG`, `writeGrandTotals_vcG`,
`writeHeaders_vcG`, `writeDetail_vcG`, `wtr_vcG`, assembled from the thin twins of their segments as
the originals are.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java


theorem writePageTotals_thinG (w ld lr : Addr) (v : WsV) :
    ThinVC Gen.prog totalsCallees.env 0 writePageTotalsRef (writePageTotalsSpecG w ld lr v) (writePageTotalsInv w ld lr v) wLineVs 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wpt_entry_t w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writePageTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact wpt_seg1_t w ld lr v args σ0 fr σ hI
  · exact wpt_seg2_t w ld lr v args σ0 fr σ hI


theorem writeAccountTotals_thinG (w ld lr : Addr) (v : WsV) :
    ThinVC Gen.prog totalsCallees.env 0 writeAccountTotalsRef (writeAccountTotalsSpecG w ld lr v) (writeAccountTotalsInv w ld lr v) wLineVs 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wat_entry_t w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeAccountTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact wat_seg1_t w ld lr v args σ0 fr σ hI
  · exact wat_seg2_t w ld lr v args σ0 fr σ hI


theorem writeGrandTotals_thinG (w ld lr : Addr) (v : WsV) :
    ThinVC Gen.prog totalsCallees.env 0 writeGrandTotalsRef (writeGrandTotalsSpecG w ld lr v) (writeGrandTotalsInv w ld lr v) wLineVs 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wgt_entry_t w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeGrandTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact wgt_seg1_t w ld lr v args σ0 fr σ hI


theorem writeHeaders_thinG (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) :
    ThinVC Gen.prog linesCallees.env 0 writeHeadersRef (writeHeadersSpecG w ld lr v xs xe rs re) (writeHeadersInv w ld lr v rs re) wLineVs 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wh_entry_t w ld lr v xs xe rs re args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeHeadersInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact wh_seg1_t w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2_t w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2a_t w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2b_t w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg3_t w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg4_t w ld lr v xs xe rs re args σ0 fr σ hI


theorem writeDetail_thinG (w ld lr : Addr) (v : WsV) (c yx cx : Addr)
    (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr) :
    ThinVC Gen.prog linesCallees.env 0 writeDetailRef (writeDetailSpecG w ld lr v c yx cx t ys cs) (writeDetailInv w ld lr v c yx cx t ys cs) wLineVs 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wd_entry_t w ld lr v c yx cx t ys cs args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeDetailInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact wd_segA_t w ld lr v c yx cx t ys cs args σ0 fr σ hI
  · exact wd_segB_t w ld lr v c yx cx t ys cs args σ0 fr σ hI
  · exact wd_seg1_t w ld lr v c yx cx t ys cs args σ0 fr σ hI


theorem wtr_thinG (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (hd : WsDateparmRecord.Valid d)
    (ht : TranRecord.Valid t) (hy : TranTypeRecord.Valid y) (hc : TranCatRecord.Valid cc)
    (hx : (Model.xAcct s.xref).natAbs < 100000000000) :
    ThinVC Gen.prog reportCalleesR.env 0 writeTransactionReportRef (wtrSpecG w ld lr c ty ca d s t y cc) (wtrInv w ld lr c ty ca d s t y cc) wLineVs 100 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wtr_entry_t w ld lr c ty ca d s t y cc args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [wtrInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact wtr_s7_t w ld lr c ty ca d s t y cc args σ0 fr σ hd hI
  · obtain ⟨hLC, hlc⟩ := lc_of_wsRel hI.1
    exact wtr_c8_t w ld lr c ty ca d s t y cc args σ0 fr σ hLC hlc hI
  · exact wtr_s12_t w ld lr c ty ca d s t y cc args σ0 fr σ hI
  · exact wtr_s13_t w ld lr c ty ca d s t y cc args σ0 fr σ hd hI
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
    exact wtr_f14_t w ld lr c ty ca d s t y cc args σ0 fr σ (tamt_lt ht) hx hcw hTA hI
  · exact wtr_s22_t w ld lr c ty ca d s t y cc args σ0 fr σ ht hy hc hI

end EquivLean.Modernize.Cbtrn03c.Java
