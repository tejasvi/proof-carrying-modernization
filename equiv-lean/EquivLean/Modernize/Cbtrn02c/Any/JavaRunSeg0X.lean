import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem jline_start : jline (Model.txt "START OF EXECUTION OF PROGRAM CBTRN02C") =
    JStr.ofString "START OF EXECUTION OF PROGRAM CBTRN02C" := by decide

theorem toNat_zero32 : (0#32 : BitVec 32).toInt.toNat = 0 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **`run` from its entry to the account copy loop** (statements 0–11): the `Result` and its
lists, the start line, the empty account table. -/
theorem run_seg0 (g : G) (σ0 : State) (cuts : Cuts) (hpre : RunPreGX g g.args σ0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c11 : cuts.lookup 11 = none)
    (c12 : cuts.lookup 12 = some (J12 g g.args σ0)) :
    RunWPcX g σ0 cuts 0 (Frame.init true g.args) σ0 := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, ⟨et3, xs3, h3, hl3, hf3⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hlen3 := forall2_length hf3
  clear hf3
  unfold RunWPcX
  jvc [runCX, inlineFuel, G.args, Grows]
  clear c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  simp only [Nat.add_assoc, Nat.reduceAdd]
  refine ⟨0#32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, by simp, Hide.intro ⟨?res, ?lists, ?tab⟩,
    ?next, ?grows, ?inits, ?statics, ?initOf⟩
  any_goals (frame_simp []; done)
  case res =>
    refine ⟨_, by chain_simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals fget_simp
  case lists =>
    refine ⟨⟨1, by chain_simp⟩, by rw [jline_start]; chain_simp, ⟨0, by chain_simp⟩, ⟨0, by chain_simp⟩,
      ⟨0, by chain_simp⟩, ⟨0, by chain_simp⟩, ⟨0, by chain_simp⟩⟩
  case tab =>
    refine ⟨[], by chain_simp, by rw [toNat_zero32, List.take_zero]; exact .nil, by simp⟩
  case next =>
    simp only [State.next_alloc, State.next_setObj]
    jomega
  case grows => grows_tac
  case inits => cls_simp
  case statics => cls_simp
  case initOf => cls_simp

end EquivLean.Modernize.Cbtrn02c.Java
