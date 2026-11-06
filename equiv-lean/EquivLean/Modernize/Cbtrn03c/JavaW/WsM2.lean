import EquivLean.Modernize.Cbtrn03c.JavaW.W3v
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM

/-!
# CBTRN03C → Java: `writeAccountTotalsM_ok`, `writeGrandTotalsM_ok`

As `writePageTotalsM_ok` (`WsM.lean`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ## `writeAccountTotals` -/

theorem writeAccountTotalsM_sat :
    Sat Gen.prog writeAccountTotalsRef Top.writeAccountTotalsSpecM := by
  intro args σ o hpre hx
  obtain ⟨w, ld, lr, d, s, hargs, hR, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, -, -, ha, -⟩ := wsAt_of_wsRel hR
  have key := writeAccountTotals_satG w ld lr v args σ o ⟨hargs, hA, ha, hi1, hi2⟩ hx
  cases o with
  | normal r σ' =>
    intro w' ld' lr' d' s' hargs' hR'
    have hw : w' = w := by
      rw [hargs] at hargs'
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
      exact hargs'.symm
    rw [hw] at hR'
    obtain ⟨v', hA', hV'⟩ := wsRel_iff.1 hR'
    obtain ⟨e1, e2, e3⟩ := wsAt_unique hA hA'
    rw [e1] at hV'
    rw [hw, e2, e3]
    obtain ⟨r1, r2, f1, f2, z1, z2, hr, hA2, hr1, hf1, hz1, hr2, hf2, hz2, hfr, hi, hs⟩ := key
    obtain ⟨fs, dm, wm, hw0, -, -, -, -, -, -, -, -, -, -, -, hldh, hlrh, -, -, -⟩ := hA
    have hk := keepsNonWs_of_frame3 hfr hw0 hldh hlrh
    refine ⟨hr, wsRel_iff.2 ⟨_, hA2, ?_⟩, hk, hi, hs⟩
    have hV0 := hV'
    obtain ⟨-, -, -, -, -, hlc, hpg, hac, hgr, -, hW, -, hlck, hpk, hak, hgk, hxk⟩ := hV0
    refine vrel_of hV' hk.2.1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hpg ?_ hgr ?_ ?_
    · show incL (incL v.lc) = BitVec.ofNat 64 (((s'.lc + 1) % 1000000000 + 1) % 1000000000)
      rw [hlc, incL_ofNat _ hlck, incL_ofNat _ (Nat.mod_lt _ (by decide))]
    · show (0#64 : BitVec 64) = BitVec.ofInt 64 0
      decide
    · show Top.RecsAt σ' (v.wrs ++ [.ref r1] ++ [.ref r2])
        ((s'.writes ++ [Model.acctTotalLine s'.acct] ++ [Model.header2]).map Top.recLine)
      simp only [List.map_append, List.map_cons, List.map_nil]
      exact top_recsAt_append (top_recsAt_append (top_recsAt_mono hk hW)
          (top_recsAt_one (top_recText_of_heap hr1 hf1 (by rw [hz1, hac, acctLine_eq hak]))))
        (top_recsAt_one (top_recText_of_heap hr2 hf2 (by rw [hz2, dashLine_eq])))
    · exact ⟨Nat.mod_lt _ (by decide), hpk, show (0 : Int).natAbs < 100000000000 by decide, hgk, hxk⟩
  | exc e σ' => exact key
  | wrong m => exact key

set_option maxHeartbeats 0 in
theorem writeAccountTotalsM_ok :
    ContractOK Gen.prog Top.writeAccountTotalsSig Top.writeAccountTotalsSpecM := by
  jcontract_ok [writeAccountTotalsM_sat]

/-! ## `writeGrandTotals` -/

theorem writeGrandTotalsM_sat : Sat Gen.prog writeGrandTotalsRef Top.writeGrandTotalsSpecM := by
  intro args σ o hpre hx
  obtain ⟨w, ld, lr, d, s, hargs, hR, hi1, hi2⟩ := hpre
  obtain ⟨v, hA, -, -, -, hg⟩ := wsAt_of_wsRel hR
  have key := writeGrandTotals_satG w ld lr v args σ o ⟨hargs, hA, hg, hi1, hi2⟩ hx
  cases o with
  | normal r σ' =>
    intro w' ld' lr' d' s' hargs' hR'
    have hw : w' = w := by
      rw [hargs] at hargs'
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
      exact hargs'.symm
    rw [hw] at hR'
    obtain ⟨v', hA', hV'⟩ := wsRel_iff.1 hR'
    obtain ⟨e1, e2, e3⟩ := wsAt_unique hA hA'
    rw [e1] at hV'
    rw [hw, e2, e3]
    obtain ⟨r1, f1, z1, hr, hA2, hr1, hf1, hz1, hfr, hi, hs⟩ := key
    obtain ⟨fs, dm, wm, hw0, -, -, -, -, -, -, -, -, -, -, -, hldh, hlrh, -, -, -⟩ := hA
    have hk := keepsNonWs_of_frame3 hfr hw0 hldh hlrh
    refine ⟨hr, wsRel_iff.2 ⟨_, hA2, ?_⟩, hk, hi, hs⟩
    have hV0 := hV'
    obtain ⟨-, -, -, -, -, hlc, hpg, hac, hgr, -, hW, -, hlck, hpk, hak, hgk, hxk⟩ := hV0
    refine vrel_of hV' hk.2.1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hlc hpg hac hgr ?_
      ⟨hlck, hpk, hak, hgk, hxk⟩
    show Top.RecsAt σ' (v.wrs ++ [.ref r1])
      ((s'.writes ++ [Model.grandTotalLine s'.grand]).map Top.recLine)
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact top_recsAt_append (top_recsAt_mono hk hW)
      (top_recsAt_one (top_recText_of_heap hr1 hf1 (by rw [hz1, hgr, grandLine_eq hgk])))
  | exc e σ' => exact key
  | wrong m => exact key

set_option maxHeartbeats 0 in
theorem writeGrandTotalsM_ok :
    ContractOK Gen.prog Top.writeGrandTotalsSig Top.writeGrandTotalsSpecM := by
  jcontract_ok [writeGrandTotalsM_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeAccountTotalsM_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeGrandTotalsM_ok
