import EquivLean.Modernize.Cbstm03a.Java.Run6.ThinLem

/-!
# CBSTM03A → Java `run`, statement 179, thin: the exit path

`trJmp > cnt`: statements 179–181, 194 (`crJmp + 1`), 195, to the cards loop (statement 168).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem t179_exit (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (crJmp cnt trJmp : I64) (v : Nat)
    (h17 : fr.get 17 = some (.long crJmp)) (h19 : fr.get 19 = some (.long cnt))
    (h22 : fr.get 22 = some (.long trJmp)) (hgt : cnt.toInt < trJmp.toInt)
    (hK : Kp (∀ fr' : Frame, fr'.get 17 = some (.long (crJmp + 1#64)) →
      (∀ i, i ∉ LoopLocals → fr'.get i = fr.get i) → runVar 168 args σ0 fr' σ < v)) :
    runThinWP g args σ0 179 fr σ v := by
  unfold runThinWP
  jvc [runCallees, runInv]
  all_goals
    refine (Kp.elim hK) _ (by simp [Frame.get_setLocal]) (fun i hi => ?_)
    simp only [LoopLocals, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨a0, a17, -, -, -, -, a26, -⟩ := hi
    simp [Frame.get_setLocal, a0, a17, a26]

end EquivLean.Modernize.Cbstm03a.Java.Seg6

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg6.t179_exit
