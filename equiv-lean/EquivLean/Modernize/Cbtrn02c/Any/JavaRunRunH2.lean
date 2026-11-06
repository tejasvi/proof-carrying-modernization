import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunH
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunCnt
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMVX

/-!
# CBTRN02C → Java: the main loop after `postTransaction`

`l65x_post`: a posted transaction with a new id brings the loop head with one more transaction
processed; `out_post_dup`: with a written id, `run`'s return holds `Model.runX`'s outputs.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem post_rejects (clk : List UInt8) (s : Model.St) (t x a : List EquivLean.Cobol.Rec.FVal) :
    (Model.St.post clk s t x a).rejects = s.rejects := by
  unfold Model.St.post; split <;> rfl

theorem post_posted (clk : List UInt8) (s : Model.St) (t x a : List EquivLean.Cobol.Rec.FVal) :
    (Model.St.post clk s t x a).posted = s.posted + 1 := by
  unfold Model.St.post; split <;> rfl

/-- The model step of a valid transaction is its posting. -/
theorem st_succ_post {g : G} {k : Nat} {x a : List EquivLean.Cobol.Rec.FVal} (_hk : k < g.trans.length)
    (hv0 : vreason g.xrefs (g.st k).accts (g.trec k) = 0)
    (hfx : Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x)
    (hfa : Model.findAcct (g.st k).accts (Model.xAcct x) = some a) :
    g.step (g.st k) (g.trec k) = Model.St.post g.clk (g.st k) (g.trec k) x a := by
  obtain ⟨x', a', hx', ha', he⟩ := step_post g.xrefs g.clk (g.st k) (g.trec k) hv0
  rw [hfx] at hx'
  cases hx'
  rw [hfa] at ha'
  cases ha'
  exact he

/-- **The loop head after a posted transaction with a new id.** -/
theorem l65x_post {g : G} {σ0 σ σ1 : State} {fr : Frame} {A : Addrs} {k : Nat} {next : I32}
    {et : JType} {xsD : List Value} {x a : List EquivLean.Cobol.Rec.FVal}
    (hL : Locs65 g A fr) (f14 : fr.get 14 = some (.int next)) (f4 : fr.get 4 = some (.int 0#32))
    (f9 : fr.get 9 = some (.long (BitVec.ofNat 64 ((k + 1) % 1000000000))))
    (f10 : fr.get 10 = some (.long (BitVec.ofNat 64 ((g.st k).rejects % 1000000000))))
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hlenD : xsD.length = g.trans.length)
    (hnext : next.toInt = k + 1) (hk : k < g.trans.length) (ha10 : g.a1 < σ0.next)
    (hstx : g.stx k = ⟨g.st k, false⟩) (hv0 : vreason g.xrefs (g.st k).accts (g.trec k) = 0)
    (hfx : Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x)
    (hfa : Model.findAcct (g.st k).accts (Model.xAcct x) = some a)
    (hnd : Model.tId (g.trec k) ∉ (g.st k).tranW.map Model.tId)
    (hMV : MV (g.st k)) (htv : DalytranRecord.Valid (g.trec k)) (hxv : CardXrefRecord.Valid x)
    (hav : AccountRecord.Valid a) (hFr : Fresh σ0 A) (hg : Grows σ0 σ)
    (hW1 : W σ1 A (Model.St.post g.clk (g.st k) (g.trec k) x a)) (hfr1 : FrameS σ σ1 (PtMod A))
    (hAd1 : ∃ xs, σ1.heap A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs))
    (hi : σ1.inits = σ0.inits) (hs : σ1.statics = σ0.statics) :
    L65X g g.args σ0 (fr.setLocal 3 (.int 0#32)) σ1 := by
  have hst := st_succ_post hk hv0 hfx hfa
  have hsucc : g.st (k + 1) = Model.St.post g.clk (g.st k) (g.trec k) x a := by
    rw [G.st_succ g hk, hst]
  have hstx1 : g.stx (k + 1) = ⟨g.st (k + 1), false⟩ := G.stx_succ_ok g hk hstx (fun h => hnd h.2)
  have hMV1 : MV (g.st (k + 1)) := by
    rw [hsucc, post_eq]; exact MV_postTr (MV_postAcc (MV_postCat hMV htv hxv) hav)
  have hrej : (g.st (k + 1)).rejects = (g.st k).rejects := by rw [hsucc, post_rejects]
  have hnotM : ∀ z, z < σ0.next → z ∉ PtMod A := by
    intro z hz hm
    have : σ0.next ≤ z := hFr z (by
      simp only [PtMod, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> simp [h])
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hz this)
  have hg1 : Grows σ0 σ1 := by
    refine ⟨Nat.le_trans hg.1 hfr1.1, fun z hz => ?_⟩
    rw [hfr1.2 z (Nat.lt_of_lt_of_le hz hg.1) (hnotM z hz), hg.2 z hz]
  obtain ⟨l32, l0, l16, l31, l8, l11, l12, l6, l13, l29, l28⟩ := hL
  refine ⟨A, k + 1, next, 0#32, BitVec.ofNat 64 ((k + 1) % 1000000000),
    BitVec.ofNat 64 ((g.st k).rejects % 1000000000), et, xsD,
    ⟨by frame_simp [l32], by frame_simp [l0], by frame_simp [l16], by frame_simp [l31],
      by frame_simp [l8], by frame_simp [l11], by frame_simp [l12], by frame_simp [l6],
      by frame_simp [l13], by frame_simp [l29], by frame_simp [l28]⟩,
    by frame_simp [f14], by frame_simp [f4], by frame_simp [f9], by frame_simp [f10],
    hfr1.heap ha1 (hnotM _ ha10), hlenD, by omega, by omega, Or.inl rfl, rfl, by rw [hrej], hstx1,
    Hide.intro ⟨by rw [hsucc]; exact hW1, hMV1, hAd1, hFr⟩, hg1, hi, hs⟩

/-- **`run`'s outputs at the abend return.** -/
theorem out_post_dup {g : G} {σ0 σ1 : State} {A : Addrs} {k : Nat} {x a : List EquivLean.Cobol.Rec.FVal}
    (hk : k < g.trans.length) (hstx : g.stx k = ⟨g.st k, false⟩)
    (hv0 : vreason g.xrefs (g.st k).accts (g.trec k) = 0)
    (hfx : Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x)
    (hfa : Model.findAcct (g.st k).accts (Model.xAcct x) = some a)
    (hdu : Model.tId (g.trec k) ∈ (g.st k).tranW.map Model.tId)
    (hWab : WAb σ1 A (dupSt (g.st k) (g.trec k) x a)) :
    runPostX g σ0 (.normal (some (.ref A.r)) σ1) := by
  have hst := st_succ_post hk hv0 hfx hfa
  have hp : (g.step (g.st k) (g.trec k)).posted = (g.st k).posted + 1 := by
    rw [hst, post_posted]
  have hx := G.stx_succ_dup g hk hstx hp hdu
  rw [hst] at hx
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := dup_fields (s := g.st k) (t := g.trec k) (x := x) (a := a)
    (clk := g.clk)
  unfold runPostX
  exact post_abend hk hx hWab e1 e2 e3 e4 e5 e6

end EquivLean.Modernize.Cbtrn02c.Java
