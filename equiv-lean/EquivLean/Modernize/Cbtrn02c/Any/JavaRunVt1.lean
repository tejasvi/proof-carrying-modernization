import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVtH

/-!
# CBTRN02C → Java: `validateTran`, statements 0 to 11

The search of the cross-reference file: none found, return 100; found, `assignXref` copies it
into `xrefWs` (to statement 11).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem vt_seg0 (d xA aD wX wA : Addr) (σ0 : State) (cuts : Cuts)
    (hpre : validateTranSpec.pre [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)
    (hc : ∀ k, 1 ≤ k → k ≤ 10 → cuts.lookup k = none)
    (c11 : cuts.lookup 11 = some (vt11 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)) :
    VtWPc [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 cuts 0
      (Frame.init true [.ref d, .ref xA, .ref aD, .ref wX, .ref wA]) σ0 := by
  have hkeepP := Hide.intro hpre
  obtain ⟨d', xA', aD', wX', wA', t, vals2, accts, fsX, fsA, hargs, hD, hIn, hX, hXk, hA, hAk,
    i1⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hkeepD := Hide.intro hD
  have hkeepI := Hide.intro hIn
  obtain ⟨fsd, sc, so, hdo, hdc, hsc, hda, hdt, hso, hol, hamt⟩ := hD
  obtain ⟨etX, xsX, etA, xsA, hxA, hlX, hshX, hfX, hvX, hnX, haD, hlA, hshA, hfA, hvA, hnA⟩ := hIn
  have hXS : XrefShapes σ0 xsX := xrefShapes_of hshX
  have hXall : ∀ v ∈ xsX, ∃ y fs, v = .ref y ∧
      σ0.heap y = some (.plain "Cbtrn02c$CardXrefRecord" fs) ∧ AllSome xrKeys fs := by
    intro v hv
    obtain ⟨x, -, hr⟩ := forall2_ex_mem hfX v hv
    obtain ⟨y, fs, rfl, hy, hf⟩ := hr
    exact ⟨y, fs, rfl, hy, by rw [← keysOf_xref2]; exact allSome_of_jrecT ⟨y, fs, rfl, hy, hf⟩ hy⟩
  clear hshX hfX hvX hshA hfA hvA hda hdt hso hol hamt
  have c1 := hc 1 (by omega) (by omega)
  have c2 := hc 2 (by omega) (by omega)
  have c3 := hc 3 (by omega) (by omega)
  have c4 := hc 4 (by omega) (by omega)
  have c5 := hc 5 (by omega) (by omega)
  have c6 := hc 6 (by omega) (by omega)
  have c7 := hc 7 (by omega) (by omega)
  have c8 := hc 8 (by omega) (by omega)
  have c9 := hc 9 (by omega) (by omega)
  have c10 := hc 10 (by omega) (by omega)
  clear hc
  rw [VtWPc_eq]
  jvc [vtCallees, findXrefSig, findXrefSpecF, findXrefSpec, assignXrefSig, assignXrefSpecF,
    Grows, narrow_long, narrow_cls]
  case right.normal.isTrue.isTrue.right.normal =>
    rename_i v σ1 hpost y hyx hfy
    obtain ⟨fs', hσ, hk⟩ := hpost wX y rfl hyx
    subst hσ
    exact vt11_of (Hide.elim hkeepD) (Hide.elim hkeepI) hsc hxA hX ‹0 ≤ firstIdx _ _›
      (List.getElem?_eq_some_iff.2 ⟨_, hyx⟩) left hk (by frame_simp []) (by frame_simp [])
      (by frame_simp []) (by frame_simp []) (by frame_simp [])
  case right.normal.isTrue.isFalse =>
    rw [arrOf_of hxA] at left hcond
    exact hcond left
  case right.normal.isFalse.left =>
    exact ⟨Nat.le_refl _, fun _ _ _ => rfl⟩
  case right.normal.isFalse.right.right.right.left =>
    rw [vt_ret100 hcond hsc ‹_› ‹_› ‹_› (cp037Str_inj hunify)]
    try rfl
  case right.normal.isFalse.right.right.right.right =>
    rename_i h0
    rw [vt_ret100 hcond hsc ‹_› ‹_› ‹_› (cp037Str_inj hunify)] at h0
    exact absurd h0 (by decide)

end EquivLean.Modernize.Cbtrn02c.Java
