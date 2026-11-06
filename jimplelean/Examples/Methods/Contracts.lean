/- The contracts of `Calc`'s methods (no bodies: a module that changes only with a contract). -/
import Jimple

open Jimple

namespace Examples.Methods

def sqSig : MethodSig := ⟨"Calc", .prim .int, "sq", [.prim .int]⟩

/-- `sq` returns the (wrapping) square and leaves the state alone. -/
def sqSpec : Spec := Spec.of
  (fun args _ => ∃ x : I32, args = [.int x])
  (fun args σ r σ' => ∀ x : I32, args = [.int x] → r = some (.int (x * x)) ∧ σ' = σ)

def sumSqSpec : Spec := Spec.of
  (fun args σ => ∃ a b : I32, args = [.int a, .int b] ∧ σ.initOf "Calc" = .done)
  (fun args _ r _ => ∀ a b : I32, args = [.int a, .int b] → r = some (.int (a * a + b * b)))

end Examples.Methods
