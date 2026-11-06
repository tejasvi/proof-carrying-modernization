import EquivLean.Modernize.Cbact04c.Every.JavaRunRes196

/-!
# CBACT04C → Java, `run`: statements 196–198 (the interest rate), a nonzero rate
-/

open Jimple EquivLean.Cobol.Rec

-- the rate comparison (`lcmp`) splits two ways, by `jlong_cmp_eq_zero_iff`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg196_rate (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J196 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) →
      Model.dRate (discD g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
        (g.trec i.toInt.toNat)) ≠ 0)
    (c197 : cuts.lookup 197 = none) (c198 : cuts.lookup 198 = none)
    (cT : cuts.lookup 199 = some (J199 g g.args σ0)) :
    RunWPc g σ0 cuts 196 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, disV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f12,
    f14, f25, f16, f17, f7, hheap, hdis⟩ := h
  have hrate := hc i f22
  clear hc
  have hin := inFacts_of_pre hpre
  obtain ⟨et4, xs4, -, -, -, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre
  have hst := stInv_st hin i.toInt.toNat hstop
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hvt := hin.tcat_valid _ hmemT
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  have hd0 := jrecAt_ne_nil (Hide.elim hdis) (by decide)
  have hvd := discD_valid hv4 hd0
  obtain ⟨dc, fsd, hdV, hdc, hrf, hr1, hr2⟩ := disRate_field (Hide.elim hdis) hvd
  subst hdV
  have hlenT : g.tcat.length < 2147483647 := by have := hin.dom.1; omega
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hR : BitVec.ofInt 64 (Model.dRate (discD g (stSel g.xrefs (g.st i.toInt.toNat)
      (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) ≠ 0#64 := by
    intro he
    exact hrate (ofInt64_inj (by omega) (by omega) (by omega) (by omega) (he.trans (by rfl)))
  have hrate' := Hide.intro hrate
  have hl2' := Hide.intro hl2
  clear hrate hst hin hvt hmemT hv4 hvd hl2 hr1 hr2 hd0
  generalize hRE : BitVec.ofInt 64 (Model.dRate (discD g (stSel g.xrefs (g.st i.toInt.toNat)
    (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) = R at hrf hR
  clear hRE
  unfold RunWPc
  jvc [runSpecG, runC, jlong_cmp_eq_zero_iff]
  -- a nonzero rate (cut point 199)
  refine ⟨i, hp, tcbV, acctV, xrefV, lastV, .ref dc, ⟨hn, hi0, ?_, ?_, ?_, ?_, ?_, htcb, hstop⟩, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hheap, hdis, Hide.elim hrate'⟩
  all_goals first
    | (locs_tac; done)
    | (frame_simp [f3, f12, f14, f25, f16, f17, f7, f22, f6, f4, f5]; done)
    | skip

end EquivLean.Modernize.Cbact04c.Java
