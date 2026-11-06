/-
Loops without a termination argument (`numloops.ts`), proved by `ts_auto` alone in partial
correctness: `JS.NoPanic` and `JS.NoFault` allow divergence, and `ts_auto` replaces a `while` or
counted `for` loop that no summary handles by its possible outcomes (`evalLoop_cases_exit`,
`StrictTS.Proof.LoopExit`): it diverges, or it ends in the same world with a completion a
function body may end with (`return` inside the loop, `throw`, the normal exit unless the loop is
`while (true)`), provided no iteration panics or changes the world (but for one cell the loop
fills) from any environment with the loop's `const` values, which symbolic execution checks.
The environments also satisfy the candidates that survive one iteration (`Env.slotsOk`): slots
the loop never assigns keep their values, and a counter that the condition reads stays a safe
natural (`hamming`: `i` indexes both strings).
-/
import Partial.NumLoopsEx
import StrictTS.Proof.Auto

open StrictTS JS NumLoopsEx

/-- A search loop with `return` inside and the bound `d * d <= n`, after a validation. -/
theorem smallestFactor_noPanic (I : Impl) (n : F64) (w : World TT) :
    JS.NoPanic (callFun I program smallestFactorRef (.cons (.num n) .nil)) w := by
  ts_auto

/-- A loop bounded by `n / 2`: no panic and no exception. -/
theorem divisorSum_noFault (I : Impl) (n : F64) (w : World TT) :
    JS.NoFault (callFun I program divisorSumRef (.cons (.num n) .nil)) w := by
  ts_auto

/-- Euclid's `while` loop. -/
theorem gcd_noPanic (I : Impl) (a b : F64) (w : World TT) :
    JS.NoPanic (callFun I program gcdRef (.cons (.num a) (.cons (.num b) .nil))) w := by
  ts_auto

/-- A loop counting down by 2 (`k -= 2`): it may run forever (`n = Infinity`), but never faults. -/
theorem oddFactorial_noFault (I : Impl) (n : F64) (w : World TT) :
    JS.NoFault (callFun I program oddFactorialRef (.cons (.num n) .nil)) w := by
  ts_auto

/-- `while (true)` left only by `return` (or the validation's `throw`). -/
theorem heronSqrt_noPanic (I : Impl) (x eps : F64) (w : World TT) :
    JS.NoPanic (callFun I program heronSqrtRef (.cons (.num x) (.cons (.num eps) .nil))) w := by
  ts_auto

/-- A loop that fills a `Set` allocated before it: the state keeps the world but for that cell
(its content is arbitrary), and the `const` slots (the `Set`'s reference). -/
theorem divisorSet_noPanic (I : Impl) (n : F64) (w : World TT) :
    JS.NoPanic (callFun I program divisorSetRef (.cons (.num n) .nil)) w := by
  ts_auto

/-- A counter that must stay a valid index (`a[i]`, `b[i]`): `ts_auto` keeps the candidate "`i` is
a natural below `2 ^ 53`" (one iteration preserves it: `i < a.length` from the condition), and the
validation gives `a.length = b.length`. Strings have fewer than `2 ^ 53` code units (ECMA-262
§6.1.4), as the hypotheses state. -/
theorem hamming_noPanic (I : Impl) (a b : Val TT .str) (w : World TT)
    (ha : a.toStr.length < 2 ^ 53) (hb : b.toStr.length < 2 ^ 53) :
    JS.NoPanic (callFun I program hammingRef (.cons a (.cons b .nil))) w := by
  ts_auto
