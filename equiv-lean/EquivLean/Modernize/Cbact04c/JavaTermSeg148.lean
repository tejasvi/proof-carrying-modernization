-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg148.lean (sha256 5878a96bd9960951...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg148
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg148`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

theorem run_tseg148_exit (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (h : J148 g g.args σ0 fr σ)
    (hc : ∀ i k : I32, fr.get 22 = some (.int (i + 1#32)) → fr.get 23 = some (.int k) →
      (g.xrefs.length : Int) ≤ k.toInt) :
    RunThinWPc g σ0 cuts 148 fr σ := by
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
