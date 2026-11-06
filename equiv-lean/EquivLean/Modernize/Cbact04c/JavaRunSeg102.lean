import EquivLean.Modernize.Cbact04c.JavaRunRes108

/-!
# CBACT04C → Java, `run`: statements 102–107 (the previous account posted)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg102 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J102 g g.args σ0 fr σ)
    (c103 : cuts.lookup 103 = none) (c104 : cuts.lookup 104 = none)
    (c105 : cuts.lookup 105 = none) (c106 : cuts.lookup 106 = none)
    (c107 : cuts.lookup 107 = none) (c108 : cuts.lookup 108 = some (J108 g g.args σ0)) :
    RunWPc g σ0 cuts 102 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hsome, hne, f3,
    f12, f14, f16, hheap⟩ := h
  have hst := stInv_st (inFacts_of_pre hpre) i.toInt.toNat
  clear hpre
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hsome
  have hne' : id ≠ Model.tAcct (g.trec i.toInt.toNat) := fun h => hne (by rw [hid, h])
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  -- the current account object: what statements 102–107 read and write
  obtain ⟨ac, fsa, hacc⟩ := acct_facts (Hide.elim hheap) (stInv_disp1 hst _) hid
  have hacc' := Hide.intro hacc
  obtain ⟨hacV, hac, hbal, ⟨w1, hw1⟩, ⟨w2, hw2⟩, h0⟩ := hacc
  subst hacV
  simp only [disp1] at hbal
  have hbr := aBal_range (acct_valid hst hid)
  have ht1 := hst.2.2.2.2.1
  have ht2 := hst.2.2.2.2.2.1
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  generalize hbalE : BitVec.ofInt 64 (Model.aBal (g.st i.toInt.toNat).acct) = bal at hbal
  generalize hTE : BitVec.ofInt 64 (g.st i.toInt.toNat).total = T at f12
  have hbalE' := Hide.intro hbalE
  have hTE' := Hide.intro hTE
  have hid' := Hide.intro hid
  have hne'' := Hide.intro hne'
  have hrng := Hide.intro (And.intro hbr (And.intro ht1 ht2))
  clear hbalE hTE hst hid hsome hne hne' hbr ht1 ht2
  unfold RunWPc
  jvc [runSpecG, runC, truncSig, fields_get_set, narrow_long]
  -- the cut point 108
  have hbalE := Hide.elim hbalE'
  have hTE := Hide.elim hTE'
  subst hbalE hTE
  obtain ⟨⟨hb1, hb2⟩, ht1, ht2⟩ := Hide.elim hrng
  refine j108_of_post hn hi0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htcb hheap (Hide.elim hid') (Hide.elim hne'')
    (Hide.elim hacc') (grows_refl _) rfl ?_ ?_ ?_
  · exact Hide.elim hlocs' |> fun hl => by
      obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hl
      exact ⟨by frame_simp [f1], by frame_simp [f36], by frame_simp [f40], by frame_simp [f8],
        by frame_simp [f37], by frame_simp [f10], by frame_simp [f19], by frame_simp [f20],
        by frame_simp [f21], by frame_simp [f41], by frame_simp [f38], by frame_simp [f26],
        by frame_simp [f24]⟩
  all_goals first
    | (frame_simp [f3, f14, f16, f22, f6, f4, f5]; done)
    | (rw [srem_add_mod _ _ 1000000000000 (by decide) (by decide) (by omega) (by omega)
        (by omega) (by omega)]
       rfl)
    | rfl
    | skip

end EquivLean.Modernize.Cbact04c.Java
