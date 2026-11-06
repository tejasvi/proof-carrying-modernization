import EquivLean.Modernize.Cbstm03b.Java.Trnx

/-!
# CBSTM03B → Java: `trnxProc`

The verification conditions of `trnxProc` for every choice of ghost values (`trnx_entry`, all paths), and its
contract against the callee contracts `seqCalleesF`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx)

namespace EquivLean.Modernize.Cbstm03b.Java

theorem trnx_vc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    MethodVC Gen.prog seqCalleesF.env 1 trnxProcRef (procSpecG ddTrnx oe st q opv oeM s a) [] 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  have h := trnx_entry oe st q opv oeM s a args σ0 hpre
  unfold trnxWP at h
  exact (by assumption)

theorem trnx_sat (hV : Valid Gen.prog seqCalleesF.env) : Sat Gen.prog trnxProcRef (procSpec ddTrnx) :=
  procSpec_of_ghost fun oe st q opv oeM s a => MethodVC.sat_of_valid hV (trnx_vc oe st q opv oeM s a)

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_vc
#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_sat
