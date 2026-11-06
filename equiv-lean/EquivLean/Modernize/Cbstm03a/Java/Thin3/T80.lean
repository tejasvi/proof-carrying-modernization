import EquivLean.Modernize.Cbstm03a.Java.Thin3.S83

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 80 (the load loop)

The paths reach the virtual cut point 83 after the three substrings of the record (`Thin3.Seg83`, continued by
`Thin3.seg83`, then `Thin3.seg93`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows GrowsK
  growsK_elim grows_split fixStr_length)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 3000000 in
set_option jimple.modelContracts true in
theorem run_thin80 (g : RunG) : RunThinCut g 80 inv80 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, h2, h3, h4, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, mem, trct, st1, s, k,
    ⟨h10, h23, h9, h6, h7, hres, hr1, hr2, hr3, hr4, hgrow, hinits, hstat⟩,
    ⟨h11, h12, h13, h14, h15, hn3, hn4, ht1x, ht2x, ht3kx, ht3x, ht4x, ht1, ht12, ht23, ht34, ht45⟩,
    ⟨h16, h24, hslots, htr, htrl⟩, h1, hst1, h4m, hmt, hts, hk, ⟨x33, h33, hx33⟩, ⟨x32, h32, hx32⟩,
    h18, h17, hbd, hmodel⟩ := hI
  obtain ⟨txs1, htxs1, htf1⟩ := ht1x
  have hl1' : txs1.length < 2147483648 := by
    rw [Forall2.length_eq htf1, RunG.T1, List.length_map, ← Forall2.length_eq hf1]; exact hl1
  simp only [List.replicate_zero, List.append_nil] at htxs1
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hcpi ⊢; rw [hinits]; exact hcpi
  have hrl : (g.R1.getD k []).length = 350 := Thin3.R1_getD_length g hk
  have hk31 : k + 1 < 2147483648 := by
    have e1 : g.R1.length = g.trs.length := by simp [RunG.R1, RunG.T1]
    have e2 : xs1.length = g.trs.length := Forall2.length_eq hf1
    omega
  have hi1 : (BitVec.ofNat 32 (k + 1)).toInt = (k + 1 : Int) := by
    rw [Thin3.ofNat32_toInt hk31]; omega
  have hv : vX80 + ((vN : Int) - (BitVec.ofNat 32 (k + 1)).toInt).toNat ≤
      runVar 80 [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 fr σ := by
    simp [runVar, arr0, h1, hst1]
  have ht1m : t1 < mem := Nat.lt_trans ht12 (Nat.lt_trans ht23 (Nat.lt_trans ht34 (Nat.lt_trans ht45 h4m)))
  generalize g.R1.getD k [] = rec at hx33 hrl
  unfold runThinWP
  refine Thin3.bodyWP_cut_insert (Thin3.callWPThin_mono _ _ 1) _ _ _ 83 (by rfl)
    (Thin3.Seg83 σ mem t1 st1 trct res txs1 (BitVec.ofNat 32 (k + 1)) s.trct) 280
    (by
      intro fr' σ' h
      exact Thin3.seg83 g _ σ0 _ σ mem t1 st1 trct res txs1 _ s.trct s.m hslots hl1' (by rw [hi1]; omega) ht1m
        hmt hts hv fr' σ' h) 20 80 fr σ ?_
  clear hv hslots hh1 hf1 h2 h3 h4 hcpa hres hgrow hinits hstat hcpi hinit htf1 ht2x ht3kx ht3x ht4x hbd hmodel
    hn3 hn4 hk hk31 hi1
  jvc [runCallees, runInv, Thin3.Seg83, StrMono]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin80
