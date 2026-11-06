import EquivLean.Modernize.Cbact04c.JavaRunRes148

/-!
# CBACT04C → Java, `run`: the cross-reference search (statement 148): exit, no match, match
-/

open Jimple EquivLean.Cobol.Rec

-- key comparisons (`lcmp`) split two ways, by `jlong_cmp_eq_zero_iff`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

/-- The cross-reference array, from the inputs, in a state grown from the entry state. -/
theorem xrefArr_of {g : G} {args : List Value} {σ0 σ : State} (hpre : RunPreG g args σ0)
    (hg : Grows σ0 σ) : ∃ xs, XrefArr g σ xs := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, hargs, -, ⟨et2, xs2, h2, -, hp2⟩, -, -, -, -, -, -, hv2, -⟩,
    -⟩ := hpre
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨-, rfl, -⟩ := hargs
  exact ⟨xs2, ⟨et2, heap_of_grows hg h2⟩, forall2_mono (fun _ _ h => jrecAt_grows hg h) hp2, hv2⟩

/-- **The search ran past the array**: impossible. -/
theorem run_seg148_exit (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J148 g g.args σ0 fr σ)
    (hc : ∀ i k : I32, fr.get 22 = some (.int (i + 1#32)) → fr.get 23 = some (.int k) →
      (g.xrefs.length : Int) ≤ k.toInt) :
    RunWPc g σ0 cuts 148 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, lastV, k, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hne, f3, f12, f14,
    f25, f16, f13, f18, f23, hk0, hkle, hprev, hcore, hacct, hlast, hfresh⟩ := h
  have hklen := hc i k f22 f23
  have hvt := trec_valid hpre hn
  have hin := inFacts_of_pre hpre
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by
    simp only [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem _
  obtain ⟨xs, hx⟩ := xrefArr_of hpre (Hide.elim hcore).1
  have hr := tAcct_range hvt
  exfalso
  obtain ⟨⟨et, hA⟩, -⟩ := id hx
  exact xref_exit_absurd hx hr.1 hr.2 (hin.dom.2 _ hmemT).2.1 (k := k.toInt.toNat) (by omega)
    (hprev et xs hA)

end EquivLean.Modernize.Cbact04c.Java
