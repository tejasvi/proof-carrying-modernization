/-
The theorem of `LoopsModProof.lean` for the whole translated program `LoopsMod.program`: the
lookups are the generated `_lookup` facts. This file is rebuilt with `LoopsMod.Program`, that
is whenever the program changes; the proof itself is not.
-/
import LoopsMod.Program
import LoopsModProof

open StrictTS JS

namespace LoopsMod

theorem maxOf_eq_maxOfReduce (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I program maxOfRef (.cons (.arr a) .nil)) w =
      exec (callFun I program maxOfReduceRef (.cons (.arr a) .nil)) w :=
  maxOf_eq_maxOfReduce_of I program maxOf_lookup maxOfReduce_lookup a xs w hw

end LoopsMod
