import EquivLean.Modernize.Cbact04c.Every.JavaRunRes108

/-!
# CBACT04C → Java, `run`: statements 113–116 (the posted account appended to the rewrites)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg113 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J113 g g.args σ0 fr σ)
    (c114 : cuts.lookup 114 = none) (c115 : cuts.lookup 115 = none)
    (c116 : cuts.lookup 116 = none) (c125 : cuts.lookup 125 = some (J125 g g.args σ0)) :
    RunWPc g σ0 cuts 113 fr σ := by
  obtain ⟨i, hp, tcbV, ac, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, hsome, hne, f3, f14, f16, hcore,
    hpst⟩ := h
  clear hpre
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨ac', fsp, hacV, hac, hfp⟩ := jrec_obj (Hide.elim hpst)
  cases hacV
  have hpres := present_keys accountRecord_jnames hfp
  obtain ⟨-, hinit, -, hres, -, -, hrw, -⟩ := Hide.elim hcore
  obtain ⟨fsR, hR, -, -, hRr, -⟩ := hres
  obtain ⟨rxs, rm, hlr, -, -⟩ := hrw
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hid' := Hide.intro hid
  clear hfp hsome hid
  have hneH := Hide.intro hne
  clear hne
  unfold RunWPc
  jvc [runSpecG, runC, copyAcctSig, Grows]
  -- the cut point 125
  first
    | (refine j125_of_rw hn hi0 hstop ?_ ?_ ?_ ?_ ?_ ?_ ?_ htcb hcore hpst (Hide.elim hid') (Hide.elim hneH)
         hac hlr ‹_› ‹_› ⟨‹_›, ‹_›⟩ ‹_›
       all_goals first
         | (locs_tac; done)
         | (frame_simp [f3, f14, f22, f6, f4, f5]; done)
         | skip)
    | skip

end EquivLean.Modernize.Cbact04c.Java
