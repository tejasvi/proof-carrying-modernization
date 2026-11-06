import EquivLean.Modernize.Cbstm03a.Java.Run2.Seg

/-!
# CBSTM03A → Java `run`, the load loop: the assertions after one table write

A `memWrite` changes only the slots array (`KeepsK (· = mem)`): the loop head's frame facts, the strings, the text
array, `trnxSt` and the counts array carry over; the slots array holds the written memory.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText space GrowsK Kept keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

theorem initOf_of_inits {σ σ' : State} (h : σ'.inits = σ.inits) (c : ClassName) :
    σ'.initOf c = σ.initOf c := by
  unfold State.initOf; rw [h]

theorem sameLocs_ne (i : Nat) (hi : i = 10 ∨ i = 23 ∨ i = 9 ∨ i = 6 ∨ i = 7 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨
    i = 15 ∨ i = 27 ∨ i = 28 ∨ i = 16 ∨ i = 24 ∨ i = 1) : i ≠ 19 ∧ i ≠ 32 := by
  omega

/-- The facts of the loop body after one `memWrite`. -/
theorem memStep {p : LP} {fr1 fr2 : Frame} {σ1 σ2 : State} (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct)
    (o3 : p.trct < p.st1) (hm : MidBase p fr1 σ1) (hr : RecLocs p fr1 σ1) {ot : Obj}
    (htr : σ1.heap p.trct = some ot)
    (hk : KeepsK (fun x => x = p.mem) σ1 σ2) (hi : σ2.inits = σ1.inits) (hs : σ2.statics = σ1.statics)
    {M : Nat → JChar} (hsl : SlotsAt σ2 p.mem M) (hf : ∀ i, i ≠ 19 → i ≠ 32 → fr2.get i = fr1.get i) :
    MidBase p fr2 σ2 ∧ RecLocs p fr2 σ2 ∧ σ2.heap p.trct = some ot := by
  obtain ⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hy, vsm, hmem⟩ := hm
  obtain ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩ := hr
  obtain ⟨k1, i1, s1, l1⟩ := Kept.elim hfk
  have hk' := keepsK_elim hk
  have hA : ArrOnly (fun x => x = p.mem) σ1 := fun y hy => ⟨_, _, hy ▸ hmem⟩
  obtain ⟨vs2, hv2, -⟩ := hsl
  refine ⟨?_, ?_, heap_keeps' hk' htr (Nat.ne_of_gt o2)⟩
  · unfold MidBase FrameK
    exact ⟨Kept.intro ⟨keeps_trans k1 (keeps_mono hk' (fun y hy => Or.inl hy)), hi.trans i1, hs.trans s1,
        fun i hi' => (hf i (sameLocs_ne i hi').1 (sameLocs_ne i hi').2).trans (l1 i hi')⟩,
      (initOf_of_inits hi _).trans hI0, (hf 11 (by decide) (by decide)).trans h11,
      heap_keeps' hk' ht1 (Nat.ne_of_lt o0), (hf 16 (by decide) (by decide)).trans h16,
      (hf 24 (by decide) (by decide)).trans h24, (hf 1 (by decide) (by decide)).trans h1,
      heap_keeps' hk' hst1 (Nat.ne_of_gt (Nat.lt_trans o2 o3)), str_keeps hk' hA hy, vs2, hv2⟩
  · unfold RecLocs
    exact ⟨xc, xi, xr, (hf 36 (by decide) (by decide)).trans h36, str_keeps hk' hA hxc,
      (hf 34 (by decide) (by decide)).trans h34, str_keeps hk' hA hxi,
      (hf 33 (by decide) (by decide)).trans h33, str_keeps hk' hA hxr⟩

theorem close95 {p : LP} {fr1 fr2 : Frame} {σ1 σ2 : State} (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct)
    (o3 : p.trct < p.st1) (hm : MidBase p fr1 σ1) (hr : RecLocs p fr1 σ1)
    (htr : σ1.heap p.trct = some (.array (.prim .long) p.L.trct)) (h18 : fr1.get 18 = some (.long p.L.cr))
    (h17 : fr1.get 17 = some (.long p.L.tr))
    (hk : KeepsK (fun x => x = p.mem) σ1 σ2) (hi : σ2.inits = σ1.inits) (hs : σ2.statics = σ1.statics)
    (hsl : SlotsAt σ2 p.mem p.m95) (hf : ∀ i, i ≠ 19 → i ≠ 32 → fr2.get i = fr1.get i)
    (h19 : fr2.get 19 = some (.long (tranOffJ p.L.cr p.L.tr))) : A95 p fr2 σ2 := by
  obtain ⟨hm2, hr2, ht2⟩ := memStep o0 o2 o3 hm hr htr hk hi hs hsl hf
  unfold A95 TabAt
  exact ⟨hm2, hr2, ⟨hsl, ht2, (hf 18 (by decide) (by decide)).trans h18,
    (hf 17 (by decide) (by decide)).trans h17⟩, h19⟩

theorem close98 {p : LP} {fr1 fr2 : Frame} {σ1 σ2 : State} (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct)
    (o3 : p.trct < p.st1) (hm : MidBase p fr1 σ1) (hr : RecLocs p fr1 σ1)
    (htr : σ1.heap p.trct = some (.array (.prim .long) p.L.trct)) (h18 : fr1.get 18 = some (.long p.L.cr))
    (h17 : fr1.get 17 = some (.long p.L.tr))
    (hk : KeepsK (fun x => x = p.mem) σ1 σ2) (hi : σ2.inits = σ1.inits) (hs : σ2.statics = σ1.statics)
    (hsl : SlotsAt σ2 p.mem p.m98) (hf : ∀ i, i ≠ 19 → i ≠ 32 → fr2.get i = fr1.get i)
    (h19 : fr2.get 19 = some (.long (tranOffJ p.L.cr p.L.tr + 16))) : A98 p fr2 σ2 := by
  obtain ⟨hm2, hr2, ht2⟩ := memStep o0 o2 o3 hm hr htr hk hi hs hsl hf
  unfold A98 TabAt
  exact ⟨hm2, hr2, ⟨hsl, ht2, (hf 18 (by decide) (by decide)).trans h18,
    (hf 17 (by decide) (by decide)).trans h17⟩, h19⟩

theorem close100 {p : LP} {fr1 fr2 : Frame} {σ1 σ2 : State} (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct)
    (o3 : p.trct < p.st1) (hm : MidBase p fr1 σ1) (hr : RecLocs p fr1 σ1)
    (htr : σ1.heap p.trct = some (.array (.prim .long) p.L.trct)) (h18 : fr1.get 18 = some (.long p.L.cr))
    (h17 : fr1.get 17 = some (.long p.L.tr))
    (hk : KeepsK (fun x => x = p.mem) σ1 σ2) (hi : σ2.inits = σ1.inits) (hs : σ2.statics = σ1.statics)
    (hsl : SlotsAt σ2 p.mem (memWr p.m98 (tranOffJ p.L.cr p.L.tr + 16).toInt (sub p.r 32 350)))
    (hf : ∀ i, i ≠ 19 → i ≠ 32 → fr2.get i = fr1.get i) {xc : Addr} (h32 : fr2.get 32 = some (.ref xc))
    (hxc : σ1.heap xc = some (.str (sub p.r 0 16))) : A100 p fr2 σ2 := by
  have hm' := hm
  obtain ⟨-, -, -, -, -, -, -, -, -, vsm, hmem⟩ := hm'
  obtain ⟨hm2, -, ht2⟩ := memStep o0 o2 o3 hm hr htr hk hi hs hsl hf
  have hA : ArrOnly (fun x => x = p.mem) σ1 := fun y hy => ⟨_, _, hy ▸ hmem⟩
  have hL : p.L.m = memWr p.m98 (tranOffJ p.L.cr p.L.tr + 16).toInt (sub p.r 32 350) := by
    unfold LP.m98 LP.m95; exact ldStep_m p.s p.r
  unfold A100 TabAt
  exact ⟨hm2, ⟨hL ▸ hsl, ht2, (hf 18 (by decide) (by decide)).trans h18,
    (hf 17 (by decide) (by decide)).trans h17⟩, xc, h32, str_keeps (keepsK_elim hk) hA hxc⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg2
