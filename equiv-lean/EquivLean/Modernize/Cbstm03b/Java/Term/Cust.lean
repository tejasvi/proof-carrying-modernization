import EquivLean.Modernize.Cbstm03b.Java.Term.CustEntry
import EquivLean.Modernize.Cbstm03b.Java.Term.CustLoop

/-!
# CBSTM03B → Java: `custProc` terminates

The termination VC (`TermVC`, cut point 49 with `custInvT` and the variant `custVarT`) from the entry paths
(`cust_tentry`) and the paths from the loop head (`cust_tloop`); the callees' contracts hold and terminate
(`custCalleesT_valid`, `custCalleesT_term`). On `procSpec ddCust`'s precondition the State object names the file
and FD record objects that `kSpecT` fixes.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

theorem cust_tvc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) :
    TermVC Gen.prog custCalleesT.env (fun _ => 0) 1 1 custProcRef
      (kSpecT ddCust "custFile" "fdCustfileRec" oe st q opv oeM s a o1 y0) (custCutsT st q o1 y0) 200 := by
  refine ⟨Gen.Cbstm03b.«custProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)», rfl,
    fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · rw [SpecEnv.below_const _ _ (by decide)]
    have h := cust_tentry oe st q opv oeM s a o1 y0 args σ0 hpre
    unfold custTWP at h
    exact h
  · intro p hp fr σ hJ
    simp only [custCutsT, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [SpecEnv.below_const _ _ (by decide)]
    have h := cust_tloop oe st q opv oeM s a o1 y0 args σ0 hpre fr σ hJ
    unfold custTWP at h
    exact h

/-- `custProc` terminates, for fixed ghost values. -/
theorem custG_term (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) :
    ∀ args σ, (kSpecT ddCust "custFile" "fdCustfileRec" oe st q opv oeM s a o1 y0).pre args σ →
      MTerm Gen.prog custProcRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) custCalleesT_valid custCalleesT_term
    (cust_tvc oe st q opv oeM s a o1 y0)

/-- **`custProc` terminates** on every input of `procSpec ddCust`. -/
theorem cust_term : ∀ args σ, (procSpec ddCust).pre args σ → MTerm Gen.prog custProcRef args σ := by
  intro args σ hpre
  obtain ⟨oe, st, q, opv, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  obtain ⟨fs, hst, -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩, -⟩ := stateAtM_iff.1 h2
  obtain ⟨o1, -, -, -, -, rfl, -⟩ := m1
  obtain ⟨y0, -, rfl, -⟩ := j1
  exact custG_term oe st q opv oeM s a o1 y0 args σ
    ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, ⟨fs, hst, g1, k1⟩⟩

set_option maxHeartbeats 4000000 in
theorem cust_cterm : ContractTerm Gen.prog custProcSig (procSpec ddCust) := by jcontract_term [cust_term]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.cust_cterm
