-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg85x.lean (sha256 08f5971aafb727d3...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg85x
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg85x`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg85_exit (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J85 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int i) → (g.tcat.length : Int) ≤ i.toInt)
    (c86 : cuts.lookup 86 = none) (c91 : cuts.lookup 91 = none) (c92 : cuts.lookup 92 = none)
    (c93 : cuts.lookup 93 = none) (c246 : cuts.lookup 246 = none) (c247 : cuts.lookup 247 = none)
    (c248 : cuts.lookup 248 = none) :
    RunThinWPc g σ0 cuts 85 fr σ := by
  obtain ⟨i, hp, acctV, xrefV, lastV, hi0, hilen, hlocs, f22, f12, f3, f14, f25, f16, f17, f4, f5,
    hheap, hstop⟩ := h
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hpre.lens
  clear hpre
  have hci := hc i f22
  clear hc
  have hiN : i.toInt.toNat = g.tcat.length := by omega
  rw [hiN] at hheap hstop
  have hres : ResAt σ hp := (Hide.elim hheap).1.2.2.2.1
  have hdisp : DispAt σ hp.ld (g.st g.tcat.length).disp := (Hide.elim hheap).1.2.2.2.2.1
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
