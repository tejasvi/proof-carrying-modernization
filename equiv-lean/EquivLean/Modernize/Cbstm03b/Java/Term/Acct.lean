import EquivLean.Modernize.Cbstm03b.Java.Term.AcctEntry
import EquivLean.Modernize.Cbstm03b.Java.Term.AcctDigit
import EquivLean.Modernize.Cbstm03b.Java.Term.AcctLoop

/-!
# CBSTM03B → Java: `acctProc` terminates

The termination VC (`TermVC`, cut points 33 and 65 with `acctInv33`, `acctInv65` and the variants `acctVar33`,
`acctVar65`) from the entry paths (`acct_tentry`) and the paths from the loop heads (`acct_tdigit`, `acct_tloop`);
the callees' contracts hold and terminate (`acctCalleesT_valid`, `acctCalleesT_term`). On `procSpec ddAcct`'s
precondition the State object names the file and FD record objects that `kSpecT` fixes.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

theorem acct_tvc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) :
    TermVC Gen.prog acctCalleesT.env (fun _ => 0) 1 1 acctProcRef
      (kSpecT ddAcct "acctFile" "fdAcctfileRec" oe st q opv oeM s a o1 y0) (acctCutsT st q o1 y0) 200 := by
  refine ⟨Gen.Cbstm03b.«acctProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)», rfl,
    fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · rw [SpecEnv.below_const _ _ (by decide)]
    have h := acct_tentry oe st q opv oeM s a o1 y0 args σ0 hpre
    unfold acctTWP at h
    exact h
  · intro p hp fr σ hJ
    simp only [acctCutsT, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [SpecEnv.below_const _ _ (by decide)]
    rcases hp with rfl | rfl
    · have h := acct_tdigit oe st q opv oeM s a o1 y0 args σ0 hpre fr σ hJ
      unfold acctTWP at h
      exact h
    · have h := acct_tloop oe st q opv oeM s a o1 y0 args σ0 hpre fr σ hJ
      unfold acctTWP at h
      exact h

/-- `acctProc` terminates, for fixed ghost values. -/
theorem acctG_term (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) :
    ∀ args σ, (kSpecT ddAcct "acctFile" "fdAcctfileRec" oe st q opv oeM s a o1 y0).pre args σ →
      MTerm Gen.prog acctProcRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) acctCalleesT_valid acctCalleesT_term
    (acct_tvc oe st q opv oeM s a o1 y0)

/-- **`acctProc` terminates** on every input of `procSpec ddAcct`. -/
theorem acct_term : ∀ args σ, (procSpec ddAcct).pre args σ → MTerm Gen.prog acctProcRef args σ := by
  intro args σ hpre
  obtain ⟨oe, st, q, opv, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  obtain ⟨fs, hst, -, -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩⟩ := stateAtM_iff.1 h2
  obtain ⟨o1, -, -, -, -, rfl, -⟩ := m1
  obtain ⟨y0, -, rfl, -⟩ := j1
  exact acctG_term oe st q opv oeM s a o1 y0 args σ
    ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, ⟨fs, hst, g1, k1⟩⟩

set_option maxHeartbeats 4000000 in
theorem acct_cterm : ContractTerm Gen.prog acctProcSig (procSpec ddAcct) := by jcontract_term [acct_term]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.acct_cterm
