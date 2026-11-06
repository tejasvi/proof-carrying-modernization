import Jimple

/-!
# Java classes with static state

A Java translation may keep a table in a static field set by the class's static initializer
(CBTRN02C's and CBTRN03C's CP037 table).  The JVM runs `<clinit>` before the first call of a static
method of the class; the statements of such programs start from a state where it has run
(`ClinitRan`), not from one where the class merely counts as initialized with arbitrary statics
(that statement would be false: the table would be any value).
-/

open Jimple

namespace EquivLean.Jimple

/-- The static initializer of class `c` has run, as the JVM runs it before the first call of a
static method of `c`: `c` is initialized, its static fields hold what `<clinit>` stored, and the
objects that existed when `<clinit>` returned are unchanged. -/
def ClinitRan (P : Program) (c : ClassName) (σ : State) : Prop :=
  σ.initOf c = .done ∧ ∃ m σ0 σ1, P.clinitOf c = some m ∧ MExec P ⟨c, m⟩ [] σ0 (.normal none σ1) ∧
    (∀ f, σ.static (c, f) = σ1.static (c, f)) ∧ (∀ x, x < σ1.next → σ.heap x = σ1.heap x)

end EquivLean.Jimple
