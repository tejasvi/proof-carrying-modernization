import EquivLean.Modernize.Cbstm03b.Java.Term.Call

/-!
# CBSTM03B → Java: total correctness

* the string helpers, outright: their contracts hold (`*_vc`) and terminate (`Term.Helpers`, `Term.KCallees`);
* the file procedures and `call`, given their contracts (`Sat`, partial correctness): they terminate on every input
  of their contracts (`trnx_term`, `xref_term`, `cust_term`, `acct_term`, `run_term`, no hypotheses).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## The helpers -/

theorem spaces_total : ∀ args σ, spacesSpec.pre args σ →
    (∃ o, MExec Gen.prog spacesRef args σ o) ∧ ∀ o, MExec Gen.prog spacesRef args σ o → spacesSpec.post args σ o :=
  total_of_sat_mterm spaces_vc.sat spaces_term
theorem zeroPad_total : ∀ args σ, zeroPadSpec.pre args σ →
    (∃ o, MExec Gen.prog zeroPadRef args σ o) ∧ ∀ o, MExec Gen.prog zeroPadRef args σ o → zeroPadSpec.post args σ o :=
  total_of_sat_mterm zeroPad_vc.sat zeroPad_term
theorem fit_total : ∀ args σ, fitSpec.pre args σ →
    (∃ o, MExec Gen.prog fitRef args σ o) ∧ ∀ o, MExec Gen.prog fitRef args σ o → fitSpec.post args σ o :=
  total_of_sat_mterm fit_vc.sat fit_term
theorem fitF_total : ∀ args σ, fitSpecF.pre args σ →
    (∃ o, MExec Gen.prog fitRef args σ o) ∧ ∀ o, MExec Gen.prog fitRef args σ o → fitSpecF.post args σ o :=
  total_of_sat_mterm fitF_vc.sat fun args σ h => fit_term args σ h
theorem status2_total : ∀ args σ, status2Spec.pre args σ →
    (∃ o, MExec Gen.prog status2Ref args σ o) ∧ ∀ o, MExec Gen.prog status2Ref args σ o → status2Spec.post args σ o :=
  total_of_sat_mterm status2_vc.sat status2_term
theorem status2F_total : ∀ args σ, status2SpecF.pre args σ →
    (∃ o, MExec Gen.prog status2Ref args σ o) ∧ ∀ o, MExec Gen.prog status2Ref args σ o → status2SpecF.post args σ o :=
  total_of_sat_mterm status2F_vc.sat fun args σ h => status2_term args σ h
theorem keySubG_total (q skey : Addr) (fs : List (FieldKey × Value)) (key : JStr) (kl : Int) :
    ∀ args σ, (keySubG q skey fs key kl).pre args σ → (∃ o, MExec Gen.prog keySubRef args σ o) ∧
      ∀ o, MExec Gen.prog keySubRef args σ o → (keySubG q skey fs key kl).post args σ o :=
  total_of_sat_mterm (keySub_vc q skey fs key kl).sat (keySubG_term q skey fs key kl)

/-! ## The file procedures, given their contracts -/

theorem trnx_total (h : Sat Gen.prog trnxProcRef (procSpec ddTrnx)) : ∀ args σ, (procSpec ddTrnx).pre args σ →
    (∃ o, MExec Gen.prog trnxProcRef args σ o) ∧
      ∀ o, MExec Gen.prog trnxProcRef args σ o → (procSpec ddTrnx).post args σ o :=
  total_of_sat_mterm h trnx_term
theorem xref_total (h : Sat Gen.prog xrefProcRef (procSpec ddXref)) : ∀ args σ, (procSpec ddXref).pre args σ →
    (∃ o, MExec Gen.prog xrefProcRef args σ o) ∧
      ∀ o, MExec Gen.prog xrefProcRef args σ o → (procSpec ddXref).post args σ o :=
  total_of_sat_mterm h xref_term
theorem cust_total (h : Sat Gen.prog custProcRef (procSpec ddCust)) : ∀ args σ, (procSpec ddCust).pre args σ →
    (∃ o, MExec Gen.prog custProcRef args σ o) ∧
      ∀ o, MExec Gen.prog custProcRef args σ o → (procSpec ddCust).post args σ o :=
  total_of_sat_mterm h cust_term
theorem acct_total (h : Sat Gen.prog acctProcRef (procSpec ddAcct)) : ∀ args σ, (procSpec ddAcct).pre args σ →
    (∃ o, MExec Gen.prog acctProcRef args σ o) ∧
      ∀ o, MExec Gen.prog acctProcRef args σ o → (procSpec ddAcct).post args σ o :=
  total_of_sat_mterm h acct_term

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.spaces_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.zeroPad_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.fit_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.fitF_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.status2_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.status2F_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.keySubG_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.cust_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.acct_total
#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.cust_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.acct_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.run_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.run_total
