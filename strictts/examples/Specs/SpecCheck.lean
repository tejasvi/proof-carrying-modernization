/-
Random testing of the JSDoc contracts before proving them: `clamp`'s contract fails on NaN
(`clamp(NaN, lo, hi)` returns NaN, which is not between `lo` and `hi`); `clampChecked`, whose
precondition excludes NaN, passes.
-/
import Specs.SpecsEx
import StrictTS.Testing

open StrictTS StrictTS.Testing SpecsEx

/-- info: some "inputs [NaN, 61, 6.4549909187025035e+47]: returns NaN | console [] | args after [NaN, 61, 6.4549909187025035e+47], and the postcondition does not hold" -/
#guard_msgs in
#eval specCheck Impl.host program clampRef clamp__requiresRef clamp__ensuresRef 2000

/-- info: none -/
#guard_msgs in
#eval specCheck Impl.host program clampCheckedRef clampChecked__requiresRef clampChecked__ensuresRef 2000
