import EquivLean.Bridge.TS.AutoCouple
import EquivLean.Demo.Gen.TS.PrOld
import EquivLean.Demo.Gen.TS.PrNew
import EquivLean.Demo.Gen.TS.DigitsOld
import EquivLean.Demo.Gen.TS.DigitsNew

/-!
# Demo: loop equivalences with a generated coupling (no invariant written)

The refactorings of `Demo/TS/PrDiff.lean` (index loop → `for … of`; early `return` → flag and
`break`) and `Demo/TS/DoWhile.lean` (`do … while` → `while (true) … break`), where the couplings
are written by hand, proved here by `equiv_ts_auto [defs]` alone (`Bridge/TS/AutoCouple.lean`):
the coupling of the two loops is generated from their states and the exit relation is the
implication between the continuations.
-/

namespace EquivLean.Demo.TS.AutoCouple
open EquivLean EquivLean.TS StrictTS
open EquivLean.Demo.Gen.TS

/-- Index loop → `for … of` (`sum`): no coupling written. -/
theorem sum_auto (I : Impl) (a : Nat) (xs : Array (Val PrOld.TT .num)) (w : World PrOld.TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·) (call I PrNew.program PrNew.sumRef (.cons (.arr a) .nil) w)
      (call I PrOld.program PrOld.sumRef (.cons (.arr a) .nil) w) := by
  equiv_ts_auto [PrOld.sum_call, PrNew.sum_call, PrOld.sumDef, PrNew.sumDef]

/-- Early `return` → flag and `break` (`contains`): no coupling written. -/
theorem contains_auto (I : Impl) (a : Nat) (v : F64) (xs : Array (Val PrOld.TT .num))
    (w : World PrOld.TT) (hw : w.heap.get? (.arr .num, a) = some xs) (hlen : xs.size < 2 ^ 32) :
    Equiv (· = ·) (call I PrNew.program PrNew.containsRef (.cons (.arr a) (.cons (.num v) .nil)) w)
      (call I PrOld.program PrOld.containsRef (.cons (.arr a) (.cons (.num v) .nil)) w) := by
  equiv_ts_auto [PrOld.contains_call, PrNew.contains_call, PrOld.containsDef, PrNew.containsDef]

/-- `do … while` → `while (true) … break` (`digits`), every `number` input: no coupling
written. -/
theorem digits_auto (I : Impl) (n : F64) (w : World DigitsOld.TT) :
    Equiv (· = ·) (call I DigitsNew.program DigitsNew.digitsRef (.cons (.num n) .nil) w)
      (call I DigitsOld.program DigitsOld.digitsRef (.cons (.num n) .nil) w) := by
  equiv_ts_auto [DigitsOld.digits_call, DigitsNew.digits_call, DigitsOld.digitsDef,
    DigitsNew.digitsDef]

end EquivLean.Demo.TS.AutoCouple
