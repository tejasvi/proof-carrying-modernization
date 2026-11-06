import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: `run` from its entry to the record-area constructor

The `Result` and its start line, the new record object and the eleven `spaces` calls, up to cut
point 22 (`J22`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem jline_startL : jline startL = JStr.ofString "START OF EXECUTION OF PROGRAM CBTRN01C" := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg0 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)) (σ0 : State)
    (hpre : runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 0
      (Frame.init true (runArgs a1 a2 a3 a4 a5 a6)) σ0 := by
  obtain ⟨-, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ := hpre
  clear hin
  unfold RunWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, spacesSpec, runArgs,
    inlineFuel, fields_get_cons, fields_get_nil, jstrLitT]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  refine ⟨σ0.next + 1 + 1 + 1, σ0.next, σ0.next + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  any_goals (trn_frame_simp []; done)
  any_goals (apply spAt_intro
             · trn_frame_simp []; rfl
             · trn_chain)
  · simp only [dalCls, dalFields0]
    trn_chain
  · refine ⟨Fields.set (Fields.set [(("Cbtrn01c$Result", "displays"), Value.null),
      (("Cbtrn01c$Result", "abended"), Value.int 0#32)] ("Cbtrn01c$Result", "displays")
      (Value.ref (σ0.next + 1))) ("Cbtrn01c$Result", "abended") (Value.int 0#32), ?_, ?_, ?_⟩
    · trn_chain
    · simp (config := { decide := true }) only [Fields.get_set, ite_true, ite_false, reduceIte]
    · simp (config := { decide := true }) only [Fields.get_set, ite_true, ite_false, reduceIte]
  · refine ⟨[.ref (σ0.next + 1 + 1)], 1, ?_, Hide.intro (.cons ⟨σ0.next + 1 + 1, rfl, ?_⟩ .nil)⟩
    · trn_chain
    · rw [jline_startL]; trn_chain
  · exact Nat.le_refl _
  · exact Nat.le_succ _
  · simp only [Nat.add_assoc]; exact Nat.le_add_right _ _
  · exact Nat.ne_of_lt (Nat.lt_succ_self _)
  · refine ⟨?_, fun x hx => ?_⟩
    · simp only [State.next_alloc, State.next_setObj] at *
      jomega
    · trn_chain
  · trn_chain

end EquivLean.Modernize.Cbtrn01c.Java
