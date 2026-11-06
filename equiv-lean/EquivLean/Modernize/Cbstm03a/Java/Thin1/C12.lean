import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 12 (the TRNXFILE texts loop)
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_thin12 (g : RunG) : RunThinCut g 12 inv12 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, h2, h3, h4, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, n, i, ⟨h10, h23, h9, h6, h7, hres, hr1, hr2, hr3, hr4, hgrow, hinits, hstat⟩,
    h11, h27, h28, hn, hi0, hin, ⟨txs, htxs, htf⟩, ht1⟩ := hI
  have ha1 : σ.heap g.a1 = some (.array et1 xs1) := heap_grows hgrow hh1
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hcpi ⊢; rw [hinits]; exact hcpi
  clear hh1 hf1 h2 h3 h4 hcpa hres hgrow hinits hstat hcpi hinit htf
  unfold runThinWP
  jvc [runCallees, runInv, runVar, locI, vN, vX12, vX24]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin12
