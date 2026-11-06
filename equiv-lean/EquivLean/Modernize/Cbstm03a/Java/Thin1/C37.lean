import EquivLean.Modernize.Cbstm03a.Java.Thin1.Lem

/-!
# CBSTM03A → Java: `run`'s thin paths from cut point 37 (the CUSTFILE loop)

The loop body calls `custText` on record `i`: its record fact is given with the record value generalized
(`t'`), so that `jvc` keeps it whole and instantiates the contract's postcondition with it.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem run_thin37 (g : RunG) : RunThinCut g 37 inv37 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, h1, h2, ⟨et3, xs3, hh3, hl3, hf3⟩, h4, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, n, i,
    ⟨h10, h23, h9, h6, h7, hres, hr1, hr2, hr3, hr4, hgrow, hinits, hstat⟩,
    h11, h12, h13, h14, h27, h30, hn, hi0, hin, ht1x, ht2x, ⟨kxs, hkxs, hkf⟩, ⟨txs, htxs, htf⟩,
    ht1, ht12, ht23, ht34⟩ := hI
  have ha3 : σ.heap g.a3 = some (.array et3 xs3) := heap_grows hgrow hh3
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hcpi ⊢; rw [hinits]; exact hcpi
  have hlen3 : xs3.length = g.crs.length := Forall2.length_eq hf3
  clear h1 h2 h4 hcpa hres hinits hstat hcpi hinit hkf ht1x ht2x
  by_cases hc : n.toInt ≤ i.toInt
  · clear hh3 hf3 hgrow htf
    unfold runThinWP
    jvc [runCallees, runInv, runVar, locI, vN, vX37, vX52]
  · have hk : i.toInt.toNat < xs3.length := by omega
    have hel1 : CustAtN σ xs3[i.toInt.toNat] (some (g.crs[i.toInt.toNat]'(by omega))) :=
      Thin1.custAtN_grows hgrow (Thin1.forall2_getElem hf3 _ hk)
    obtain ⟨t', hel⟩ : ∃ t' : Option CustR, CustAtN σ xs3[i.toInt.toNat] t' := ⟨_, hel1⟩
    have htl : txs.length = i.toInt.toNat := by
      rw [Forall2.length_eq htf, List.length_take, RunG.T3, List.length_map]; omega
    obtain ⟨L, hL, hkL⟩ : ∃ L : List Value, σ.heap t3 = some (.array (.cls "java.lang.String") L) ∧
        i.toInt.toNat < L.length := ⟨_, htxs, by simp only [List.length_append, List.length_replicate]; omega⟩
    clear hel1 hh3 hf3 hgrow htf htxs htl
    unfold runThinWP
    jvc [runCallees, runInv, runVar, locI, vN, vX37, Grows, Thin1.getElem?_set_self_of_lt, List.length_append,
      List.length_replicate]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin37
