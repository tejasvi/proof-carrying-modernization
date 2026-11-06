/-
`examples/Async/words.ts`: an external tokenizer `splitWords(s: string): string[]` (declared in
`node_modules/fakestr`; `WordsEx.lean` was produced by the translator of the `frontend` branch).
The oracle answers with the elements of a fresh array (`.ok (.arr …)`); the call allocates that
array at the next address, and the program reads it like one of its own.
-/
import Async.WordsEx
import StrictTS.Proof.Extern
import StrictTS.Proof.Tactics

open StrictTS JS WordsEx

/-- `splitWords(s: string): string[]` -/
abbrev splitWords : ExtFun := ⟨"fakestr:splitWords", [.str], .arr .str⟩

/-- The answer `[a, b]` is allocated at the next address with these contents, and
`parts.length` is `2`. -/
theorem countWords_two (I : Impl) (w : World TT) (s a b : JSStr)
    (h : w.answer splitWords (.cons (.str s) .nil) w.extIdx =
      .ok (.arr (.cons (.val (.str a)) (.cons (.val (.str b)) .nil)))) :
    exec (callFun I program countWordsRef (.cons (.str s) .nil)) w =
      some (.ok (.num 2),
        { w with heap := w.heap.insert (.arr .str, w.next) #[.str a, .str b], next := w.next + 1,
                 extIdx := w.extIdx + 1 }) := by
  rw [countWords_call]
  simp [countWordsDef, ts_sym, h]

/-- `parts[0]` is the first element of the answer. -/
theorem firstWord_first (I : Impl) (w : World TT) (s a b : JSStr)
    (h : w.answer splitWords (.cons (.str s) .nil) w.extIdx =
      .ok (.arr (.cons (.val (.str a)) (.cons (.val (.str b)) .nil)))) :
    exec (callFun I program firstWordRef (.cons (.str s) .nil)) w =
      some (.ok (.str a),
        { w with heap := w.heap.insert (.arr .str, w.next) #[.str a, .str b], next := w.next + 1,
                 extIdx := w.extIdx + 1 }) := by
  rw [firstWord_call]
  simp [firstWordDef, ts_sym, h]

/-- For every answer list `ws`, `parts.length` is its length. -/
theorem countWords_length (I : Impl) (w : World TT) (s : JSStr) (ws : List (Val TT .str))
    (h : w.answer splitWords (.cons (.str s) .nil) w.extIdx = .ok (.arr (EVals.ofList ws))) :
    exec (callFun I program countWordsRef (.cons (.str s) .nil)) w =
      some (.ok (.num (F64.ofNat ws.length)),
        { w with heap := w.heap.insert (.arr .str, w.next) ws.toArray, next := w.next + 1,
                 extIdx := w.extIdx + 1 }) := by
  rw [countWords_call]
  simp [countWordsDef, ts_sym, h]
