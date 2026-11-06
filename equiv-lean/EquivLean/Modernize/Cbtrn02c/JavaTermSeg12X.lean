-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermSeg12X.lean (sha256 9205a1dc797c021a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg12X
import EquivLean.Modernize.Cbtrn02c.JavaTermDefs

/-!
# CBTRN02C → Java, termination: thin twin of `run_seg12` (`JavaRunSeg12X`)

The statement and the preamble of the original over the thin cut list (each cut assertion a variant
comparison), its two cases (the account table complete; one more account copied), each with the
original's `jvc` call; calls by `callWPThin`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_tseg12 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J12 g g.args σ0 fr σ)
    (c13 : cuts.lookup 13 = none) (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none)
    (c16 : cuts.lookup 16 = none) (c17 : cuts.lookup 17 = none) (c18 : cuts.lookup 18 = none)
    (c19 : cuts.lookup 19 = none) (c20 : cuts.lookup 20 = none) (c21 : cuts.lookup 21 = none)
    (c12 : cuts.lookup 12 = some (fun fr' σ' => runVs 12 g.args σ0 fr' σ' < runVs 12 g.args σ0 fr σ))
    (c22 : cuts.lookup 22 = some (fun fr' σ' => runVs 22 g.args σ0 fr' σ' < runVs 12 g.args σ0 fr σ)) :
    RunThinWPcX g σ0 cuts 12 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, ⟨et3, xs3, h3, hl3, hf3⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨i, f32, f0, f7, f2, f16, f31, f8, f15, hi0, hil, hH, hnext, hg, hinits, hstat, hinit⟩ := h
  have hg' := Hide.intro hg
  have hlen3 := forall2_length hf3
  have h3' := heap_of_grows hg h3
  obtain ⟨hR, hL, ys, hT, hF, hB⟩ := Hide.elim hH
  have hR' := Hide.intro hR
  have hL' := Hide.intro hL
  have hF' := Hide.intro hF
  have hB' := Hide.intro hB
  have hys : ys.length = i.toInt.toNat := by
    rw [forall2_length hF, List.length_take]; omega
  have hiA : σ.initOf "Cbtrn02c$AccountRecord" = .done := by
    rw [show σ.initOf "Cbtrn02c$AccountRecord" = σ0.initOf "Cbtrn02c$AccountRecord" by
      simp only [State.initOf, hinits]]
    exact i3
  clear hR hL hB
  by_cases hc : (g.accts.length : Int) ≤ i.toInt
  · clear hf3 hF
    have hiE : i.toInt.toNat = g.accts.length := by omega
    clear hg
    unfold RunThinWPcX
    jvc [runCX, inlineFuel, G.args, Grows, runVs]
  · have hn : i.toInt.toNat < xs3.length := by omega
    have hrec := forall2_get hf3 _ hn (by omega)
    obtain ⟨y, fs, hy, hyh, -⟩ := id hrec
    rw [hy] at hrec
    have hall : AllSome acKeys fs := by
      rw [← keysOf_acct']; exact allSome_of_jrec hrec hyh
    have hget : xs3[i.toInt.toNat]? = some (.ref y) := by
      rw [List.getElem?_eq_getElem hn, hy]
    have hyh' := heap_of_grows hg hyh
    have hrec' := Hide.intro hrec
    clear hf3 hF hrec
    clear hg
    unfold RunThinWPcX
    jvc [runCX, inlineFuel, G.args, Grows, copyAccountSigT, copyAccountSpecF, runVs]

end EquivLean.Modernize.Cbtrn02c.Java
