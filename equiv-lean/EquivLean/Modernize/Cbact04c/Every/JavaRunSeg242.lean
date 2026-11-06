import EquivLean.Modernize.Cbact04c.Every.JavaRunRes242

/-!
# CBACT04C → Java, `run`: statements 242–245 (write the transaction, next record)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg242 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J242 g g.args σ0 fr σ)
    (c243 : cuts.lookup 243 = none) (c244 : cuts.lookup 244 = none) (c245 : cuts.lookup 245 = none)
    (c85 : cuts.lookup 85 = some (J85 g g.args σ0)) :
    RunWPc g σ0 cuts 242 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, hset⟩ := h
  have hin := inFacts_of_pre hpre
  have hlenT : g.tcat.length < 2147483647 := by have := hin.dom.1; omega
  clear hpre hin
  obtain ⟨fsT, hT, -⟩ := Hide.elim hset
  have hL := Hide.elim hheap
  obtain ⟨-, hinit, -, hres, -, hw, -, -, htr, -⟩ := hL.1
  obtain ⟨fsR, hR, -, hRw, -, -⟩ := hres
  obtain ⟨wxs, wm, hlw, -, -⟩ := hw
  obtain ⟨fs0, hT0, hTk, -, -⟩ := htr
  rw [hT] at hT0
  cases hT0
  have hpres : ∀ k ∈ keysRC, ∃ v, Fields.get fsT ("Cbact04c$TranRecord", k) = some v := hTk
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hT' := Hide.intro hT
  have hlw' := Hide.intro hlw
  clear hTk hL
  unfold RunWPc
  jvc [runSpecG, runC, copyTranSig, Grows]
  apply j85_of_write hn hi0 hstop hlenT hheap hrate hset (Hide.elim hT') (Hide.elim hlw')
  case hy0 => assumption
  case hy => assumption
  case hk => assumption
  case hg => exact ⟨by assumption, by assumption⟩
  case hi => assumption
  case hlocs => locs_tac
  case f22 => frame_simp [f22]
  case f12 => frame_simp [f12]
  case f3 => frame_simp [f3]
  case f14 => frame_simp [f14]
  case f25 => frame_simp [f25]
  case f16 => frame_simp [f16]
  case f17 => frame_simp [f17]
  case f4 => frame_simp [f4]
  case f5 => frame_simp [f5]

end EquivLean.Modernize.Cbact04c.Java
