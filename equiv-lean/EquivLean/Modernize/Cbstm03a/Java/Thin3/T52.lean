import EquivLean.Modernize.Cbstm03a.Java.Thin3.S61

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 52 (the ACCTFILE loop)

The loop path stores `acctText(acctFile[i#78])` and goes back to 52 with `i#78 + 1`; the exit path reaches the
virtual cut point 61 (`Thin3.Seg61`, continued by `Thin3.seg61`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows GrowsK
  growsK_elim grows_split fixStr_length)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem run_thin52 (g : RunG) : RunThinCut g 52 inv52 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, h2, h3, ⟨et4, xs4, hh4, hl4, hf4⟩, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, n3, n, i,
    ⟨h10, h23, h9, h6, h7, hres, hr1, hr2, hr3, hr4, hgrow, hinits, hstat⟩,
    h11, h12, h13, h14, h15, h27, h28, h26, hn3, hn, hi0, hin, ⟨txs1, htxs1, htf1⟩, ht2x, ht3kx, ht3x,
    ⟨txs4, htxs4, htf4⟩, ht1, ht12, ht23, ht34, ht45⟩ := hI
  have hl1' : txs1.length < 2147483648 := by
    rw [Forall2.length_eq htf1, RunG.T1, List.length_map, ← Forall2.length_eq hf1]; exact hl1
  simp only [List.replicate_zero, List.append_nil] at htxs1
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hcpi ⊢; rw [hinits]; exact hcpi
  have ha4 : σ.heap g.a4 = some (.array et4 xs4) := heap_grows hgrow hh4
  have hv : vX80 + vN < runVar 52 [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 fr σ := by
    simp only [runVar, locI, h26]; unfold vX52; omega
  clear hh1 hf1 h2 h3 hcpa hres hgrow hinits hstat hcpi hinit htf1 htf4 ht2x ht3kx ht3x hh4 hf4
  unfold runThinWP
  refine Thin3.bodyWP_cut_insert (Thin3.callWPThin_mono _ _ 1) _ _ _ 61 (by rfl) (Thin3.Seg61 t1 res txs1) 200
    (by intro fr' σ' h; exact Thin3.seg61 g _ σ0 _ t1 res txs1 hl1' hv fr' σ' h) 100 52 fr σ ?_
  clear hv
  jvc [runCallees, runInv, runVar, locI, vN, vX52, vX80, vM, vC3, vC4, vK, Thin3.Seg61, Thin3.rep2]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin52
