import EquivLean.Modernize.Cbstm03a.Java.Final

/-!
# CBSTM03A → Java

* `java : Statement`: the generated statement (`Java.Final.java_statement`).
* `java_terminates`, `java_total`: from `runSpec`'s precondition, `run` terminates, and it ends normally with
  `runSpec`'s postcondition (total correctness), the callees' termination contracts linked in `Java.Terms`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- **CBSTM03A → Java.** -/
theorem java : Statement := java_statement

/-- `run` terminates from every state satisfying `runSpec`'s precondition. -/
theorem java_terminates : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ :=
  runSpec_term_of_J (run_term_of runCalleeSats runCalleeTerms run_segs run_thin_segs)

/-- Total correctness of `run` for `runSpec`. -/
theorem java_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  runSpec_total_of run_sat java_terminates

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.java
#print axioms EquivLean.Modernize.Cbstm03a.Java.java_terminates
#print axioms EquivLean.Modernize.Cbstm03a.Java.java_total
