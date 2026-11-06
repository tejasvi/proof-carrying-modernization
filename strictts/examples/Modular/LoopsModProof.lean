/-
A proof on the translator's modular output (`--modular`, see `frontend/README.md`): it imports
only the `Defs` modules of the two functions it is about, and holds for every program `P` that
has their definitions at their references' indices (`hf`, `hg`). Its .olean therefore survives
edits to the other functions of `examples/Summarize/loops.ts`, and additions and removals of
functions. `LoopsModProgram.lean` instantiates it for the translated program.
-/
import LoopsMod.Defs.maxOf
import LoopsMod.Defs.maxOfReduce
import StrictTS.Proof.Summarize

open StrictTS JS

namespace LoopsMod

/-- The loop and the `reduce` agree on every array and every world, in every program that
contains the two functions. -/
theorem maxOf_eq_maxOfReduce_of (I : Impl) (P : Program TT)
    (hf : P.funs[maxOfRef.idx]? = some maxOfDef) (hg : P.funs[maxOfReduceRef.idx]? = some maxOfReduceDef)
    (a : Nat) (xs : Array (Val TT .num)) (w : World TT) (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I P maxOfRef (.cons (.arr a) .nil)) w =
      exec (callFun I P maxOfReduceRef (.cons (.arr a) .nil)) w := by
  rw [maxOf_call_of I P hf, maxOfReduce_call_of I P hg]
  simp only [maxOfDef, maxOfReduceDef, ts_sym]
  ts_summarize
  ts_callbacks
  simp [ts_sym]

end LoopsMod
