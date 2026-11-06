import EquivLean.Modernize.Cbact04c.JavaRunRunLemmas

/-!
# CBACT04C → Java, `run`: the entry path, statements 0–9 (the `Result`, the start line)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg0 (g : G) (σ0 : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = some (J10 g g.args σ0)) :
    RunWPc g σ0 cuts 0 (Frame.init true g.args) σ0 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre.2.2
  clear hpre
  unfold RunWPc
  jvc [runSpecG, runC, inlineFuel, fields_get_cons, fields_get_nil, G.args]
  -- the `Result` and its lists are built, the start line displayed
  unfold J10
  refine ⟨σ0.next, σ0.next + 1, σ0.next + 1 + 1, σ0.next + 1 + 1 + 1, σ0.next + 1 + 1 + 1 + 1, ?_⟩
  repeat' apply And.intro
  all_goals first
    | (exact Hide.intro ⟨_, by chain_simp, by simp [fields_get_set, fields_get_cons],
        by simp [fields_get_set, fields_get_cons], by simp [fields_get_set, fields_get_cons],
        by simp [fields_get_set, fields_get_cons]⟩)
    | resid_close

end EquivLean.Modernize.Cbact04c.Java
