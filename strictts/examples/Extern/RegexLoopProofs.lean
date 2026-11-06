/-
A `for … of` loop over the host's match results (`regexloop.ts`), proved by `ts_auto` in partial
correctness: the loop runs over the fresh array of matches; each iteration calls the host twice
(`m.index`, `m[0]`) and changes the world only in its external-call counter, so the fallback for
`for … of` loops (`evalForOf_cases_exit`) applies. The hypotheses are the host's guarantees from
ECMA-262 (`World.MatchAllFresh`, `World.MatchElementZero`, `StrictTS.Proof.Extern`); without
`MatchElementZero` the statement is false (`m[0]!` panics on a host that answers `undefined`).
-/
import Extern.RegexLoopEx
import StrictTS.Proof.Auto

open StrictTS JS RegexLoopEx

set_option maxHeartbeats 1000000 in
/-- No panic (the host may throw). -/
theorem prefixLines_noPanic (I : Impl) (text pre : Val TT .str) (w : World TT)
    (ht : text.toStr.length < 2 ^ 53) (hp : pre.toStr.length < 2 ^ 53)
    (hall : w.MatchAllFresh) (h0 : w.MatchElementZero) :
    JS.NoPanic (callFun I program prefixLinesRef (.cons text (.cons pre .nil))) w := by
  ts_auto
