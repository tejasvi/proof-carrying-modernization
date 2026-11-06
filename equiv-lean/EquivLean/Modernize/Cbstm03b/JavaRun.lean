import EquivLean.Modernize.Cbstm03b.Java.Link
import EquivLean.Modernize.Cbstm03b.Java.TrnxVC
import EquivLean.Modernize.Cbstm03b.Java.Xref
import EquivLean.Modernize.Cbstm03b.Java.CustAll
import EquivLean.Modernize.Cbstm03b.Java.AcctProc
import EquivLean.Modernize.Cbstm03b.Java.Term.Total

/-!
# CBSTM03B → Java: the generated statement, and total correctness

`java`: the generated per-call statement for the Java translation (`JavaStatement.lean`), from the contract of
`Cbstm03b.call` (`JavaProof.runSpec`, by `statement_of_sat`): every terminating run of `call` from related values
ends with related values. `java_terminates`: on every input of the contract `call` terminates, so `java_total`:
it has an outcome and every outcome satisfies the contract (total correctness).

The contract is proved bottom-up (`Java/*.lean`): the string helpers (`HSpaces`, `HZeroPad`, `HFit`, `HStatus2`,
`HKeySub`, `HFresh`), the four file procedures against them (`TrnxVC`, `Xref`, `CustAll`, `AcctProc`, each for
every choice of the contract's ghost values, `procSpecG`), `call`'s dispatch against the procedures
(`CallVC`), and the link (`Link`: `run_sat_of`). Termination (`Java/Term/*.lean`): thin twins of every method with
ranks at the loop heads, linked bottom-up through the callees' termination contracts (`Term.Call`: `run_term`).
-/

open Jimple
open CardDemo.Cbstm03b (ddCust)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- The callee contracts `custProc` is verified against hold. -/
theorem custCalleesFP_valid : Valid Gen.prog CustP.custCalleesF.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [CustP.custCalleesF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact status2F_ok
  · exact fitF_ok
  · exact keySub_ok
  · exact spaces_ok)

theorem cust_sat : Sat Gen.prog custProcRef (procSpec ddCust) :=
  procSpec_of_ghost fun oe st q opv oeM s a =>
    MethodVC.sat_of_valid custCalleesFP_valid (custProc_vc oe st q opv oeM s a)

/-- The contract of `call` holds (partial correctness). -/
theorem run_sat : Sat Gen.prog callRef runSpec :=
  run_sat_of (trnx_sat seqCalleesF_valid) (xref_sat seqCalleesF_valid) cust_sat (AcctP.acct_sat acctCallees_valid)

/-- **CBSTM03B → Java**: the generated statement. -/
theorem java : Statement := statement_of_sat run_sat

/-- `call` terminates on every input of its contract. -/
theorem java_terminates : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog callRef args σ := run_term

/-- **CBSTM03B → Java, total correctness**: on every input of `call`'s contract there is an outcome, and every
    outcome satisfies the contract. -/
theorem java_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog callRef args σ o) ∧ ∀ o, MExec Gen.prog callRef args σ o → runSpec.post args σ o :=
  run_total run_sat

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.java
#print axioms EquivLean.Modernize.Cbstm03b.Java.java_terminates
#print axioms EquivLean.Modernize.Cbstm03b.Java.java_total
