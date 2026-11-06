import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 24 (the XREFFILE texts loop)
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_thin24 (g : RunG) : RunThinCut g 24 inv24 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, h1, ⟨et2, xs2, hh2, hl2, hf2⟩, h3, h4, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, n, i, ⟨h10, h23, h9, h6, h7, hres, hr1, hr2, hr3, hr4, hgrow, hinits, hstat⟩,
    h11, h12, h27, h29, hn, hi0, hin, ht1x, ⟨txs, htxs, htf⟩, ht1, ht12⟩ := hI
  have ha2 : σ.heap g.a2 = some (.array et2 xs2) := heap_grows hgrow hh2
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hcpi ⊢; rw [hinits]; exact hcpi
  clear hh2 hf2 h1 h3 h4 hcpa hres hgrow hinits hstat hcpi hinit htf ht1x
  unfold runThinWP
  jvc [runCallees, runInv, runVar, locI, vN, vX24, vX37]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin24
