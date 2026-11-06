import EquivLean.Modernize.Cbstm03a.Java.Thin2.Wp

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 117 (the cross-reference loop)

The record read (`seqRead`) moves `xrefSt[0]` from `j` to `j + 1` ("00") or sets the end flag ("10", the loop
exits); the paths reach 140 (variant: one record less, plus the customer search) or return. The "00" path is split
at statement 126 (after `fix`), where the record text is taken as an unknown string of 1000 characters.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Thin2

/-- Statement 126 of a record read (after `fix`): `xrefSt` = `{j + 1, 0}`, `tId` clear, the customers' count in
`$i20`, the record text (1000 characters) in `cn`. -/
def A126 (st2 : Addr) (jv n3 : I32) : Frame → State → Prop := fun fr σ =>
  fr.get 2 = some (.ref st2) ∧ σ.heap st2 = some (.array (.prim .int) [.int jv, .int 0]) ∧
    fr.get 3 = some (.int 0) ∧ fr.get 27 = some (.int n3) ∧
    ∃ x s, fr.get 33 = some (.ref x) ∧ HeapIs σ x (.str s) ∧ s.length = 1000

end Thin2

open Thin2 in
theorem run_thin117 (g : RunG) : RunThinCut g 117 inv117 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨-, -, ⟨et2, xs2, -, hl2, hF2⟩, -, -, ⟨hci0, -⟩, -⟩ := hpre
  have hx2 : g.xrs.length < 2147483648 := by rw [← Forall2.length_eq hF2]; exact hl2
  clear hF2 hl2
  obtain ⟨res, ld, ls, lh, L, o, j, hX, hjl, -⟩ := hI
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hbase, htexts, -, h2, hst2, -, -, -, h5, h3, -, -⟩ := hX
  obtain ⟨-, -, -, -, h7, -, -, -, -, -, -, hinits, -⟩ := hbase
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hci0 ⊢; rw [hinits]; exact hci0
  clear hinits hci0
  obtain ⟨-, h12, -, -, -, ⟨n3, h27, -⟩, -, -, ⟨x2t, hT2, hF2t⟩, -, -, -, -, ht12, ht23, ht34, ht45⟩ :=
    htexts
  simp only [List.replicate_zero, List.append_nil] at hT2
  have hl2t : x2t.length = g.T2.length := Forall2.length_eq hF2t
  have hT2l : g.T2.length = g.xrs.length := by simp [RunG.T2]
  have hj : j < 2147483648 := by omega
  have ht2st2 : t2 ≠ st2 := by
    intro e; subst e; rw [hT2] at hst2; cases hst2
  have hv : runVar 117 args σ0 fr σ = ((vN : Int) - (j : Int)).toNat * vM := by
    simp only [runVar, arr0, h2, hst2, bv32_toInt_ofNat_of_lt hj]
  rw [hv]
  unfold runThinWP
  rcases (Nat.lt_or_ge j x2t.length).symm with hout | hin
  · have hl2b : x2t.length < 2147483648 := by omega
    clear hF2t hT2l hx2 hl2t
    have hT2g := heapIs_of_agree hT2
    have hst2g := heapIs_of_agree hst2
    jvc [runCallees, runInv, runVar, locI, arr0, vN, vM, vC3, vC4, vK, Grows, Keeps, seqCode, seqStArr,
      fixStr_length]
  · obtain ⟨e2, s2, he2, hs2⟩ := texts_elem hF2t j hin
    have hj1 : j + 1 < 2147483648 := by omega
    have hl2b : x2t.length < 2147483648 := by omega
    have hjv : (BitVec.ofNat 32 j + 1#32).toInt = (j : Int) + 1 := by
      have e : BitVec.ofNat 32 j + 1#32 = BitVec.ofNat 32 (j + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [e, bv32_toInt_ofNat_of_lt hj1]
      omega
    clear hF2t hT2l hx2 hjl hl2t
    refine bodyWP_cut (callWPThin_mono runCallees.env 1) runBodyA _ _ 126 ?_
      (A126 st2 (BitVec.ofNat 32 j + 1#32) n3) 150 (fun fr' σ' hA => ?_) 150 117 fr σ ?_
    · simp [runInv]
    · -- 126 → 140: the record's fields cut out of the text
      obtain ⟨h2', hst2', h3', h27', x, s, h33, hs, hsl⟩ := hA
      unfold HeapIs at hs
      clear h2 hst2 h5 h3 h7 h12 h27 hT2 he2 hs2 hci ht12 ht23 ht34 ht45 ht2st2 hin hl2b
      jvc [runCallees, runInv, runVar, locI, arr0, vN, vM, vC3, vC4, vK]
    · -- 117 → 126: the record read
      have hT2g := heapIs_of_agree hT2
      have hst2g := heapIs_of_agree hst2
      jvc [runCallees, runInv, runVar, locI, arr0, vN, vM, vC3, vC4, vK, Grows, Keeps, seqCode, seqStArr, A126]
      all_goals exact ⟨_, ‹_›, fixStr_length _ _⟩

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin117
