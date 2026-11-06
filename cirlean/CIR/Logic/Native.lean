import CIR.Logic.WP

/-!
  Test theorems by evaluation.

  `callReturnsB ctx sym args m p` runs the call and checks its return value
  with a Boolean test `p`. If it evaluates to `true`, the call terminates
  without undefined behaviour and returns a value satisfying `p`
  (`returns_of_callReturnsB`). For concrete calls (test functions, from
  `module.initMem`) the check can be evaluated:
  * `cir_native` uses `native_decide` (fast; trusts the compiler, axiom
    `Lean.ofReduceBool`).
-/

namespace CIR

/-- The call returns normally, and its value passes the test `p`. -/
def callReturnsB (ctx : Ctx) (sym : String) (args : List Val) (m : Mem) (p : Option Val → Bool) : Bool :=
  match evalCall ctx sym args m with
  | .ok (.ret v, _) => p v
  | _ => false

theorem returns_of_callReturnsB {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {p : Option Val → Bool} (h : callReturnsB ctx sym args m p = true) :
    Returns ctx sym args m (fun v _ => p v = true) := by
  unfold callReturnsB at h
  unfold Returns Calls
  split at h
  · rename_i v m' heq
    rw [heq]; exact h
  · exact absurd h Bool.false_ne_true

/-- The test "returns the integer `k`". -/
def isInt (k : Int) : Option Val → Bool
  | some (.int x) => x == k
  | _ => false

theorem isInt_eq_true {k : Int} {v : Option Val} : isInt k v = true ↔ v = some (.int k) := by
  cases v with
  | none => simp [isInt]
  | some v => cases v <;> simp [isInt]

/-- A test function that returns the integer `k`. -/
theorem returns_int_of_callReturnsB {ctx : Ctx} {sym : String} {args : List Val} {m : Mem} {k : Int}
    (h : callReturnsB ctx sym args m (isInt k) = true) :
    Returns ctx sym args m (fun v _ => v = some (.int k)) := by
  have := returns_of_callReturnsB h
  unfold Returns Calls at *
  exact Res.holds_mono this (fun r hr => by
    rcases r with ⟨e, m'⟩
    cases e <;> simp_all [isInt_eq_true])

end CIR

/-- `cir_native` proves `Returns ctx sym args m (fun v _ => v = some (.int k))`
for a concrete call by running it (`native_decide`). -/
macro "cir_native" : tactic =>
  `(tactic| (apply CIR.returns_int_of_callReturnsB; native_decide))
