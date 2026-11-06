/-
Concrete test cases proved by execution (`ts_eval`): translator output of `concrete.ts`, the shapes
of verif-orchestrator's es-toolkit test cases (`median` with a sort over literals, `lerp` with
`0.5`/`0.25`, `%` and `.length`, a `while` loop, `Math.round`/`Math.pow`). Each theorem says that
the test function returns normally from the initialised module world, i.e. that every expectation
holds, for every implementation `I` of the implementation-approximated functions.
-/
import StrictTS.Proof.Eval
import Concrete.ConcreteEx

open StrictTS StrictTS.JS ConcreteEx

namespace ConcreteEx

/-- `median([5, 2, 1, 4, 3]) === 3`: `slice().sort((a, b) => a - b)` runs on the literals. -/
theorem testMedianOdd_returns (I : Impl) :
    JS.Returns (callFun I program «testMedianOddRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `median([1, 2, 3, 4]) === 2.5`: `(2 + 3) / 2` on doubles. -/
theorem testMedianEven_returns (I : Impl) :
    JS.Returns (callFun I program «testMedianEvenRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `median([])` is `NaN`. -/
theorem testMedianEmpty_returns (I : Impl) :
    JS.Returns (callFun I program «testMedianEmptyRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `lerp` with fractions `0.5`, `0.25`, `0.75` (exact binary fractions). -/
theorem testLerp_returns (I : Impl) :
    JS.Returns (callFun I program «testLerpRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `lerp` outside `[0, 1]`: `1.5`, `-0.5`, `2`. -/
theorem testLerpOutside_returns (I : Impl) :
    JS.Returns (callFun I program «testLerpOutsideRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- A `for … of` loop testing `x % 2 === 0`, unrolled on `[1, …, 7]`, and `xs.length % 2 === 1`. -/
theorem testCountEven_returns (I : Impl) :
    JS.Returns (callFun I program «testCountEvenRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `0.1 + 0.2` is within `5e-6` of `0.3` but not within `5e-21`: the `while` loop computing
`10^20` is unrolled twenty times. -/
theorem testClose_returns (I : Impl) :
    JS.Returns (callFun I program «testCloseRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- `round(1.5) === 2`, `round(1.4) === 1`, `round(-1.5) === -1`, `round(0) === 0`: the default
precision `0` makes `Math.pow(10, 0)` the specified `1` (`x ** ±0 = 1`), whatever `I.pow` is. -/
theorem testRound_returns (I : Impl) :
    JS.Returns (callFun I program «testRoundRef» .nil) (Testing.initWorld I program) := by
  ts_eval

/-- With precision `2`, `Math.pow(10, 2)` is implementation-approximated (ECMA-262 fixes only the
special cases): the test holds for every implementation that computes `10 ** 2 = 100`. -/
theorem testRoundPrecision_returns (I : Impl) (hpow : I.pow (F64.ofNat 10) (F64.ofNat 2) = F64.ofNat 100) :
    JS.Returns (callFun I program «testRoundPrecisionRef» .nil) (Testing.initWorld I program) := by
  ts_eval [hpow]

end ConcreteEx
