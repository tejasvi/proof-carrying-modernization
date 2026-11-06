import EquivLean.Modernize.Cbact04c.JavaRunRes125

/-!
# CBACT04C → Java, `run`: statements 125–128 (the new account id's text)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg125 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J125 g g.args σ0 fr σ)
    (c126 : cuts.lookup 126 = none) (c127 : cuts.lookup 127 = none) (c128 : cuts.lookup 128 = none)
    (c129 : cuts.lookup 129 = some (J129 g g.args σ0)) : RunWPc g σ0 cuts 125 fr σ := by
  obtain ⟨i, hp, tcbV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hne, f3, f14, hcore⟩ := h
  have hvt := trec_valid hpre hn
  clear hpre
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  obtain ⟨fsy, tyA, fiA, hyh, ht0, -, -, -, -, -, -, hr0, hr1, -, -, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  have hta := toInt_ofInt64 (v := Model.tAcct (g.trec i.toInt.toNat)) (by omega) (by omega)
  have ba : -9223372036854775808 < (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt := by
    rw [hta]; omega
  have hinit : Inits σ := (Hide.elim hcore).2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hta' := Hide.intro hta
  clear hvt hr0 hr1 hta
  generalize haE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at ht0 ba
  have haE' := Hide.intro haE
  clear haE
  have hneH := Hide.intro hne
  clear hne
  unfold RunWPc
  jvc [runSpecG, runC, fmtUSig, Grows]
  -- the cut point 129
  have haE := Hide.elim haE'
  subst haE
  have hta := Hide.elim hta'
  refine j129_of_fmt (yl := w) hn hi0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htcb (Hide.elim hneH) hcore ?_
    ⟨‹_›, ‹_›⟩ ‹_›
  · exact Hide.elim hlocs' |> fun hl => by
      obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hl
      exact ⟨by frame_simp [f1], by frame_simp [f36], by frame_simp [f40], by frame_simp [f8],
        by frame_simp [f37], by frame_simp [f10], by frame_simp [f19], by frame_simp [f20],
        by frame_simp [f21], by frame_simp [f41], by frame_simp [f38], by frame_simp [f26],
        by frame_simp [f24]⟩
  all_goals first
    | (frame_simp [f3, f14, f22, f6, f4, f5]; done)
    | (rw [← hta]; assumption)
    | skip

end EquivLean.Modernize.Cbact04c.Java
