-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg242.lean (sha256 31a953f39d7408fd...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg242
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg242`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg242 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J242 g g.args σ0 fr σ)
    (c243 : cuts.lookup 243 = none) (c244 : cuts.lookup 244 = none) (c245 : cuts.lookup 245 = none)
    (c85 : cuts.lookup 85 = some (fun fr' σ' => runVs B 85 g.args σ0 fr' σ' < runVs B 242 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 242 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f11,
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
  unfold RunThinWPc
  jvc [runSpecG, runC, copyTranSig, Grows, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
