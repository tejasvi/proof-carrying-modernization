import EquivLean.Modernize.Cbact04c.Every.JavaRunRunLemmas

/-!
# CBACT04C → Java, `run`: the entry path, statements 10–27 (the lengths, the table array)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg10 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J10 g g.args σ0 fr σ)
    (c11 : cuts.lookup 11 = none) (c12 : cuts.lookup 12 = none) (c13 : cuts.lookup 13 = none)
    (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none) (c16 : cuts.lookup 16 = none)
    (c17 : cuts.lookup 17 = none) (c18 : cuts.lookup 18 = none) (c19 : cuts.lookup 19 = none)
    (c20 : cuts.lookup 20 = none) (c21 : cuts.lookup 21 = none) (c22 : cuts.lookup 22 = none)
    (c23 : cuts.lookup 23 = none) (c24 : cuts.lookup 24 = none) (c25 : cuts.lookup 25 = none)
    (c26 : cuts.lookup 26 = none) (c27 : cuts.lookup 27 = none)
    (c28 : cuts.lookup 28 = some (J28 g g.args σ0)) :
    RunWPc g σ0 cuts 10 fr σ := by
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
  unfold RunWPc
  jvc [runSpecG, runC]
  -- the copy loop's head: nothing copied yet
  unfold J28
  refine ⟨0#32, res, ld, lw, lr, σ.next, [], ?_⟩
  repeat' apply And.intro
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f24, f10]; done)
    | (exact Hide.intro .nil)
    | (exact Hide.intro (resAt_agree (resAt_congr (Hide.elim hres))
        (agree_of_grows [] (grows_alloc _ _)) (List.not_mem_nil)))
    | (exact Hide.intro (dispAt_start g.accts (by rw [State.heap_alloc, ite_eq_right (by assumption)]; exact hld)
        (by rw [State.heap_alloc, ite_eq_right (by assumption)]; exact hsv)))
    | (simp only [BitVec.toInt_zero]; omega)
    | (intro x hx; rw [State.heap_alloc, if_neg (by omega)]; simp_all)
    | state_simp
    | resid_close

end EquivLean.Modernize.Cbact04c.Java
