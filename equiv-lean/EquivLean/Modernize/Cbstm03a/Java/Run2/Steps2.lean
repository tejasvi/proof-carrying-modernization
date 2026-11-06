import EquivLean.Modernize.Cbstm03a.Java.Run2.Orig

/-!
# CBSTM03A → Java `run`, the load loop: the assertions after `setTrct`

`setTrct` changes only the counts array (`KeepsK (· = trct)`): everything else of the loop body's facts carries over.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText space GrowsK Kept keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The facts of the loop body after `setTrct` (statement 88). -/
theorem trctStep {p : LP} {fr1 fr2 : Frame} {σ1 σ2 : State} (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct)
    (o3 : p.trct < p.st1) (hm : MidBase p fr1 σ1) (hr : RecLocs p fr1 σ1) {M : Nat → JChar}
    (hsl : SlotsAt σ1 p.mem M) {vt : List Value} (htr : σ1.heap p.trct = some (.array (.prim .long) vt))
    (hk : KeepsK (fun x => x = p.trct) σ1 σ2) (hi : σ2.inits = σ1.inits) (hs : σ2.statics = σ1.statics)
    (hf : ∀ i, i ≠ 18 → i ≠ 17 → fr2.get i = fr1.get i) :
    MidBase p fr2 σ2 ∧ RecLocs p fr2 σ2 ∧ SlotsAt σ2 p.mem M := by
  obtain ⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hy, vsm, hmem⟩ := hm
  obtain ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩ := hr
  obtain ⟨k1, i1, s1, l1⟩ := Kept.elim hfk
  have hk' := keepsK_elim hk
  have hA : ArrOnly (fun x => x = p.trct) σ1 := fun y (hy0 : y = p.trct) => by subst hy0; exact ⟨_, _, htr⟩
  refine ⟨?_, ?_, slotsAt_keeps hk' hA hsl (Nat.ne_of_lt o2)⟩
  · unfold MidBase FrameK
    exact ⟨Kept.intro ⟨keeps_trans k1 (keeps_mono hk' (fun y hy => Or.inr (Or.inl hy))), hi.trans i1,
        hs.trans s1, fun i hi' => (hf i (sameLocs_ne11 i hi').2.2.2.2.2.2.2.2.1
          (sameLocs_ne11 i hi').2.2.2.2.2.2.2.1).trans (l1 i hi')⟩,
      (initOf_of_inits hi _).trans hI0, (hf 11 (by decide) (by decide)).trans h11,
      heap_keeps' hk' ht1 (Nat.ne_of_lt (Nat.lt_trans o0 o2)), (hf 16 (by decide) (by decide)).trans h16,
      (hf 24 (by decide) (by decide)).trans h24, (hf 1 (by decide) (by decide)).trans h1,
      heap_keeps' hk' hst1 (Nat.ne_of_gt o3), str_keeps hk' hA hy, vsm, heap_keeps' hk' hmem (Nat.ne_of_lt o2)⟩
  · unfold RecLocs
    exact ⟨xc, xi, xr, (hf 36 (by decide) (by decide)).trans h36, str_keeps hk' hA hxc,
      (hf 34 (by decide) (by decide)).trans h34, str_keeps hk' hA hxi,
      (hf 33 (by decide) (by decide)).trans h33, str_keeps hk' hA hxr⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg2
