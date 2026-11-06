-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg28c.lean (sha256 446eff7e687d8153...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg28c
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg28c`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg28 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J28 g g.args σ0 fr σ)
    (c29 : cuts.lookup 29 = none) (c30 : cuts.lookup 30 = none) (c31 : cuts.lookup 31 = none)
    (c32 : cuts.lookup 32 = none) (c33 : cuts.lookup 33 = none) (c34 : cuts.lookup 34 = none)
    (c35 : cuts.lookup 35 = none) (c36 : cuts.lookup 36 = none) (c37 : cuts.lookup 37 = none)
    (c28 : cuts.lookup 28 = some (fun fr' σ' => runVs B 28 g.args σ0 fr' σ' < runVs B 28 g.args σ0 fr σ)) (c38 : cuts.lookup 38 = some (fun fr' σ' => runVs B 38 g.args σ0 fr' σ' < runVs B 28 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 28 fr σ := by
  obtain ⟨-, hin, -⟩ := hpre
  obtain ⟨b1, b2, b3, b4, q1, c1, hargs, -, -, ⟨et3, xs3, h3, hp3⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨j, res, ld, lw, lr, A, cxs, f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f22, f41,
    f18, hj0, hjlen, hcxlen, hA, hcopies, hres, hdisp, hlw, hlr, hr0, hd0, hw0, hl0, hA0, hd1,
    hd2, hd3, hg, i1, i2, i3, i4, i5, i6, i7, i8⟩ := h
  obtain ⟨hb3, hp3⟩ := hp3
  have hlen3 : xs3.length = g.accts.length := Forall2.length_eq hp3
  have h3' : σ.heap g.a3 = some (.array et3 xs3) := heap_of_grows hg h3
  by_cases hc : (g.accts.length : Int) ≤ j.toInt
  · -- the copy is complete: the first record object (statements 34–37)
    clear hp3
    unfold RunThinWPc
    jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, ctorTCSig, ctorTCF, runVs, upAt]
    all_goals first
      | exact ⟨Or.inl rfl, rfl⟩
      | skip
  · -- one more account copied
    have hn : j.toInt.toNat < xs3.length := by omega
    have hrec : JRecAt AccountRecord "Cbact04c$AccountRecord" σ0 xs3[j.toInt.toNat]
        (g.accts[j.toInt.toNat]'(by omega)) := forall2_getElem hp3 _ hn
    obtain ⟨y, fs, hy, hyheap, hyf⟩ := jrec_obj hrec
    have hpres := present_keys accountRecord_jnames hyf
    have hget : xs3[j.toInt.toNat]? = some (.ref y) := by
      rw [List.getElem?_eq_getElem hn, hy]
    have hyheap' : σ.heap y = some (.plain "Cbact04c$AccountRecord" fs) := heap_of_grows hg hyheap
    rw [hy] at hrec
    have hrec' := Hide.intro hrec
    clear hp3 hrec hyf
    unfold RunThinWPc
    jvc [runSpecG, runC, inlineFuel, Grows, copyAcctSig, runVs, upAt]
    all_goals first
      | exact ⟨Or.inl rfl, rfl⟩
      | skip

end EquivLean.Modernize.Cbact04c.Java
