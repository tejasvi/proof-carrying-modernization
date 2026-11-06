/-
  Examples/Exceptions.lean

  Structured exception handling as Jimple keeps it: `Hello.safeDiv(int,int)` is
      try { return a / b; } catch (ArithmeticException e) { return -1; } finally { cnt++; }
  which Soot turns into four typed traps (the `finally` code duplicated on every path,
  plus catch-all `Throwable` handlers that rethrow). The contract covers the
  division-by-zero exception raised by the JVM, its dispatch through the trap table by
  class hierarchy, the class-initialization check of `Hello`, and the static counter.
-/
import Jimple

open Jimple

jimple_import "examples_java/hello/jimple" as Ex

namespace Examples.Exceptions

def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

/-- safeDiv(a, b): a / b, or -1 when b = 0 (ArithmeticException caught); the `finally`
    block increments the static counter `cnt` on every path. -/
def safeDivSpec : Spec := Spec.of
  (fun args σ => ∃ a b c : I32, args = [.int a, .int b] ∧ σ.initOf "Hello" = .done ∧
     σ.static ("Hello", "cnt") = some (.int c))
  (fun args σ r σ' => ∀ a b c : I32, args = [.int a, .int b] → σ.static ("Hello", "cnt") = some (.int c) →
     r = some (.int (if b = 0 then -1 else a.sdiv b)) ∧ σ'.static ("Hello", "cnt") = some (.int (c + 1)))

set_option maxRecDepth 8000 in
theorem safeDiv_ok : MethodVC Ex.prog (fun _ => none) 0 (mref Ex.prog "Hello" "safeDiv") safeDivSpec [] 60 := by
  jverify

end Examples.Exceptions

#print axioms Examples.Exceptions.safeDiv_ok
