import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVtH2

/-!
# CBTRN02C → Java: `validateTran`, statements 11 to 17

The search of the account table: none found, return 101; found, `assignAccount` copies it into
`acctWs` (to statement 17).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

attribute [local irreducible] VtD VtIn

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem vt_seg11 (d xA aD wX wA : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : validateTranSpec.pre [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)
    (h : vt11 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr σ)
    (hc : ∀ k, 12 ≤ k → k ≤ 16 → cuts.lookup k = none)
    (c17 : cuts.lookup 17 = some (vt17 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)) :
    VtWPc [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 cuts 11 fr σ := by
  have hkeepP := Hide.intro hpre
  obtain ⟨d', xA', aD', wX', wA', t, vals2, accts, fsX, fsA, hargs, hD, hIn, hX, hXk, hA, hAk,
    i1⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨fsX', v, f2, f1, f0, f9, f5, rfl, hv, hkeepX⟩ := h d xA aD wX wA rfl
  have hkeepD := Hide.intro hD
  have hkeepI := Hide.intro hIn
  unfold VtD at hD
  unfold VtIn at hIn
  obtain ⟨fsd, sc, so, hdo, hdc, hsc, hda, hdt, hso, hol, hamt⟩ := hD
  obtain ⟨etX, xsX, etA, xsA, hxA, hlX, hshX, hfX, hvX, hnX, haD, hlA, hshA, hfA, hvA, hnA⟩ := hIn
  have hAS : AcctShapes σ0 xsA := acctShapes_of hshA
  have hAall : ∀ v ∈ xsA, ∃ y fs, v = .ref y ∧
      σ0.heap y = some (.plain "Cbtrn02c$AccountRecord" fs) ∧ AllSome acKeys fs := by
    intro v hv
    obtain ⟨x, -, hr⟩ := forall2_ex_mem hfA v hv
    obtain ⟨y, fs, rfl, hy, hf⟩ := hr
    exact ⟨y, fs, rfl, hy, by rw [← keysOf_acct2]; exact allSome_of_jrecT ⟨y, fs, rfl, hy, hf⟩ hy⟩
  have hwXA : wA ≠ wX := by
    intro he
    rw [he, hX] at hA
    simp at hA
  clear hshX hfX hvX hshA hfA hvA hda hdt hso hol hamt hdc hsc hdo
  have c12 := hc 12 (by omega) (by omega)
  have c13 := hc 13 (by omega) (by omega)
  have c14 := hc 14 (by omega) (by omega)
  have c15 := hc 15 (by omega) (by omega)
  have c16 := hc 16 (by omega) (by omega)
  clear hc
  rw [VtWPc_eq]
  jvc [vtCallees, findAccountSig, findAccountSpecF, findAccountSpec, assignAccountSig,
    assignAccountSpecF, Grows, narrow_long, narrow_cls]
  case left.isFalse =>
    refine ⟨etA, xsA, ⟨rfl, rfl⟩, hlA, acctShapes_setObj_cls hAS (fun fs h => ?_)⟩
    rw [hX] at h
    simp at h
  case right.normal.isTrue.isFalse.isTrue.left.right.isFalse =>
    exact hAk
  case right.normal.isTrue.isFalse.isTrue.right.normal =>
    rename_i vv σ1 hpost y hyx hfy
    obtain ⟨fs', hσ, hk⟩ := hpost wA y rfl hyx
    subst hσ
    exact vt17_of hX hA haD hwXA (Hide.elim hkeepX) ‹0 ≤ firstIdx _ _›
      (List.getElem?_eq_some_iff.2 ⟨_, hyx⟩) left hk (by frame_simp [f2]) (by frame_simp [f5])
  case right.normal.isTrue.isFalse.isFalse =>
    have harr : arrOf (σ0.setObj wX (Obj.plain "Cbtrn02c$CardXrefRecord" fsX')) aD = xsA :=
      arrOf_of (by rw [State.heap_setObj_of_lt (State.lt_next_of_heap hX), if_neg ‹¬aD = wX›]; exact haD)
    rw [harr] at left hcond
    exact hcond left
  case right.normal.isFalse.left =>
    exact ⟨by rw [State.next_setObj]; exact Nat.le_refl _, fun z hz hm => by
      rw [State.heap_setObj, if_neg (fun h => hm (by simp [h]))]⟩
  case right.normal.isFalse.right.left =>
    exact (Hide.elim hkeepX).1 _ ‹_›
  case right.normal.isFalse.right.right.right.left =>
    rw [vt_ret101 hX haD (Hide.elim hkeepX) ‹¬0 ≤ firstIdx _ _› ‹VtD _ _ _› ‹VtIn _ _ _ _ _ _ _›]
    try rfl
  case right.normal.isFalse.right.right.right.right =>
    rename_i h0
    rw [vt_ret101 hX haD (Hide.elim hkeepX) ‹¬0 ≤ firstIdx _ _› ‹VtD _ _ _› ‹VtIn _ _ _ _ _ _ _›] at h0
    exact absurd h0 (by decide)

end EquivLean.Modernize.Cbtrn02c.Java
