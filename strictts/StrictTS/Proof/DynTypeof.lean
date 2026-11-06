import StrictTS.Lib.Dyn

/-!
# The answers of `typeof` on an unknown value

`typeof x` on `x : unknown` has finitely many answers, and each says something about the runtime type
(`Dyn.base`). A program that stores the answer, e.g. `const type = typeof value` at the type of the
eight `typeof` strings, converts it to a string-literal union case by comparing it with each case, so a
proof about such a program splits on the answer (`typeof_cases`, the difftool's `dt_typeof_cases`):
in each case the comparisons decide, and the runtime-type equation decides `=== null` and the casts.
`"object"` is split on whether the value is `null` (`typeof null` is `"object"`).
-/

namespace StrictTS.Dyn

variable {TT : TypeTable}

/-- The answers of `typeof`, with what each says about the runtime type. -/
theorem typeof_cases (v : Val TT .dyn) :
    (Dyn.typeof v = none ∧ ∃ n, (Dyn.base v).1 = .ext n) ∨
    (Dyn.typeof v = some (JSStr.ofString "number") ∧ (Dyn.base v).1 = .num) ∨
    (Dyn.typeof v = some (JSStr.ofString "bigint") ∧ (Dyn.base v).1 = .bigint) ∨
    (Dyn.typeof v = some (JSStr.ofString "boolean") ∧ (Dyn.base v).1 = .bool) ∨
    Dyn.typeof v = some (JSStr.ofString "string") ∨
    (Dyn.typeof v = some (JSStr.ofString "undefined") ∧ (Dyn.base v).1 = .undef) ∨
    (Dyn.typeof v = some (JSStr.ofString "function") ∧ ∃ a r, (Dyn.base v).1 = .fn a r) ∨
    (Dyn.typeof v = some (JSStr.ofString "object") ∧ (Dyn.base v).1 = .null) ∨
    (Dyn.typeof v = some (JSStr.ofString "object") ∧ (Dyn.base v).1 ≠ .null) := by
  unfold Dyn.typeof
  cases h : (Dyn.base v).1 <;> simp [Dyn.typeofBase]

end StrictTS.Dyn
