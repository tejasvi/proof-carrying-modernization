-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg10c.lean (sha256 2b73d65f8df5936e...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg10c
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg10c`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg10 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J10 g g.args σ0 fr σ)
    (c11 : cuts.lookup 11 = none) (c12 : cuts.lookup 12 = none) (c13 : cuts.lookup 13 = none)
    (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none) (c16 : cuts.lookup 16 = none)
    (c17 : cuts.lookup 17 = none) (c18 : cuts.lookup 18 = none) (c19 : cuts.lookup 19 = none)
    (c20 : cuts.lookup 20 = none) (c21 : cuts.lookup 21 = none) (c22 : cuts.lookup 22 = none)
    (c23 : cuts.lookup 23 = none) (c24 : cuts.lookup 24 = none) (c25 : cuts.lookup 25 = none)
    (c26 : cuts.lookup 26 = none) (c27 : cuts.lookup 27 = none)
    (c28 : cuts.lookup 28 = some (fun fr' σ' => runVs B 28 g.args σ0 fr' σ' < runVs B 10 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 10 fr σ := by
  obtain ⟨-, hin, -⟩ := hpre
  obtain ⟨b1, b2, b3, b4, q1, c1, hargs, ⟨et1, xs1, h1, hb1, hp1⟩, ⟨et2, xs2, h2, hb2, hp2⟩,
    ⟨et3, xs3, h3, hb3, hp3⟩, ⟨et4, xs4, h4, hb4, hp4⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hl1 := Forall2.length_eq hp1
  have hl2 := Forall2.length_eq hp2
  have hl3 := Forall2.length_eq hp3
  have hl4 := Forall2.length_eq hp4
  clear hp1 hp2 hp3 hp4
  obtain ⟨res, ld, lw, lr, sv, f1, f36, f40, f8, f37, f24, f10, hres, hld, hsv, hlw, hlr, hr0, hd0,
    hw0, hl0, hd1, hd2, hd3, hg, i1, i2, i3, i4, i5, i6, i7, i8⟩ := h
  have h1' := heap_of_grows hg h1
  have h2' := heap_of_grows hg h2
  have h3' := heap_of_grows hg h3
  have h4' := heap_of_grows hg h4
  unfold RunThinWPc
  jvc [runSpecG, runC, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
