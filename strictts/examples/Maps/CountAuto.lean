/-
`examples/Maps/count.ts` without a loop invariant: `ts_summarize` computes the loop's effect on
the `Map` cell (one `set` per word, the `get` with `??` merged into one value by case analysis
on the lookup), so the function's result is a pure fold over the words.
-/
import Maps.CountEx
import StrictTS.Proof.Summarize

open StrictTS JS CountEx

/-- One iteration of the loop, as computed by `ts_summarize`. -/
def countStep (m : JSMap (Val TT .str) (Val TT .num)) (x : Val TT .str) : JSMap (Val TT .str) (Val TT .num) :=
  m.set (Conv.svz .str) x (.num ((Merge.optCase (m.get? (Conv.svz .str) x) 0 (fun v => v.toNum)) + 1))

/-- `countWords` returns a fresh `Map` whose content is the fold of `countStep` over the words,
and changes nothing else (every world, every array). -/
theorem countWords_summary (I : Impl) (a : Nat) (xs : Array (Val TT .str)) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some xs) :
    exec (callFun I program countWordsRef (.cons (.arr a) .nil)) w =
      some (.ok (.map w.next),
        { w with heap := w.heap.insert (.map .str .num, w.next) (xs.toList.foldl countStep {}),
                 next := w.next + 1 }) := by
  rw [countWords_call]
  simp only [countWordsDef, ts_sym]
  ts_summarize
  simp [ts_sym]
  rfl
