import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: the read loop after the end of file

The end message, and the `Result` is returned: the lines of `Model.displayText`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem jline_endL : jline endL = JStr.ofString "END OF EXECUTION OF PROGRAM CBTRN01C" := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The loop head after the end of file: the end message, and the `Result` is returned. -/
theorem run_seg29_exit (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (d : Value) (res l : Addr) (fs : List (FieldKey × Value))
    (ys : List Value) (m : Nat)
    (f5 : fr.get 5 = some (.int 1#32)) (f9 : fr.get 9 = some (.ref res))
    (f11 : fr.get 11 = some (.ref l))
    (hres : σ.heap res = some (.plain "Cbtrn01c$Result" fs))
    (hfd : Fields.get fs ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hfa : Fields.get fs ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hrl : res ≠ l) (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((headL vals1 vals3 vals5 vals1.length true).map jline))) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 29 fr σ := by
  unfold RunWP
  jvc [runInv, runSpecG, runPostG, callees, runArgs, inlineFuel, fields_get_cons, fields_get_nil,
    jstrLitT]
  have hl' : ∀ o, (σ.alloc o).2.heap l = some (.list .arrayList ys m) := fun o => by
    rw [State.heap_alloc, ite_eq_right (State.ne_next_of_heap hl), hl]
  -- (JimpleLean 1546Z's jvc already picks these witnesses)
  try refine ⟨.arrayList, ys ++ [.ref σ.next], ⟨Nat.lt_succ_of_lt (State.lt_next_of_heap hl), rfl, rfl⟩,
    ?_⟩
  rw [← headL_final, List.map_append, List.map_singleton]
  refine forall2_append_one ?_ (forall2_mono (fun _ _ h => jstrAt_setObj_list (hl' _)
    (jstrAt_of_grows (grows_alloc _ _) h)) (Hide.elim hD))
  refine ⟨σ.next, rfl, ?_⟩
  rw [State.heap_setObj, ite_eq_right (Ne.symm (State.ne_next_of_heap hl)), State.heap_alloc, ite_eq_left rfl]
  congr 2

end EquivLean.Modernize.Cbtrn01c.Java
