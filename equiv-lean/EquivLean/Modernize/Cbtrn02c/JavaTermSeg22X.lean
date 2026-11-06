-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg22X.lean (sha256 d8fcd2c5e67e11fa...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg22X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twin of `run_seg22` (`JavaRunSeg22X`)

The statement and the preamble of the original over the thin cut list (each cut assertion a variant
comparison), its two cases (the category list complete; one more category record copied), each
with the original's `jvc` call; calls by `callWPThin`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_tseg22 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J22 g g.args σ0 fr σ)
    (c23 : cuts.lookup 23 = none) (c24 : cuts.lookup 24 = none) (c25 : cuts.lookup 25 = none)
    (c26 : cuts.lookup 26 = none) (c27 : cuts.lookup 27 = none) (c28 : cuts.lookup 28 = none)
    (c29 : cuts.lookup 29 = none) (c30 : cuts.lookup 30 = none) (c31 : cuts.lookup 31 = none)
    (c32 : cuts.lookup 32 = none) (c33 : cuts.lookup 33 = none) (c34 : cuts.lookup 34 = none)
    (c22 : cuts.lookup 22 = some (fun fr' σ' => runVs 22 g.args σ0 fr' σ' < runVs 22 g.args σ0 fr σ))
    (c35 : cuts.lookup 35 = some (fun fr' σ' => runVs 35 g.args σ0 fr' σ' < runVs 22 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 22 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, -, ⟨et4, xs4, h4, hl4, hf4⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨i, c, f32, f0, f2, f16, f31, f8, f11, f15, hi0, hil, hH, hnext, hg, hinits, hstat, hinit⟩ := h
  have hg' := Hide.intro hg
  have hlen4 := forall2_length hf4
  have h4' := heap_of_grows hg h4
  obtain ⟨hR, hL, hTab, ⟨xs, m, hc, hF, hB⟩, hc9⟩ := Hide.elim hH
  have hR' := Hide.intro hR
  have hL' := Hide.intro hL
  have hTab' := Hide.intro hTab
  have hF' := Hide.intro hF
  have hB' := Hide.intro hB
  have hclt : c < σ.next := State.lt_next_of_heap hc
  clear hR hL hTab hB hH
  by_cases hcnd : (g.cats.length : Int) ≤ i.toInt
  · -- the list complete: `lK`, `xrefWs` (statements 29–34)
    have hiE : i.toInt.toNat = g.cats.length := by omega
    have hiX : σ.initOf "Cbtrn02c$CardXrefRecord" = .done := by rw [initOf_of_inits3 hinits]; exact i4
    clear hf4 hF hg
    unfold RunThinWPcX
    jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorXRSig, ctorXRSpec,
      fields_get_cons, fields_get_nil, runVs]
  · -- one more category record copied
    have hn : i.toInt.toNat < xs4.length := by omega
    have hrec := forall2_get hf4 _ hn (by omega)
    obtain ⟨y, fs, hy, hyh, -⟩ := id hrec
    rw [hy] at hrec
    have hall : AllSome tcKeys fs := by
      rw [← keysOf_tcat']; exact allSome_of_jrec' hrec hyh
    have hget : xs4[i.toInt.toNat]? = some (.ref y) := by
      rw [List.getElem?_eq_getElem hn, hy]
    have hyh' := heap_of_grows hg hyh
    have hrec' := Hide.intro hrec
    have hiT : σ.initOf "Cbtrn02c$TranCatBalRecord" = .done := by rw [initOf_of_inits3 hinits]; exact i6
    clear hf4 hF hrec hg
    unfold RunThinWPcX
    jvc [runCX, inlineFuel, G.args, Grows, copyTcatSigT, copyTcatSpecF, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
