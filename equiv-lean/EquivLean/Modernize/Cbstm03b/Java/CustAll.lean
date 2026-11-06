import EquivLean.Modernize.Cbstm03b.Java.CustEntry
import EquivLean.Modernize.Cbstm03b.Java.CustEntryK
import EquivLean.Modernize.Cbstm03b.Java.CustEntryK2
import EquivLean.Modernize.Cbstm03b.Java.CustSeg53
import EquivLean.Modernize.Cbstm03b.Java.CustSeg80

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

/-- The entry path, by the operation and the file's state. -/
theorem cust_entry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  by_cases hO : Model.aOp a = opOpen
  · cases hb : s.cust.isOpen
    · cases he : oeM 3 with
      | none => exact ce_open00 oe st q opv oeM s a args σ0 hpre hO hb he
      | some c => exact ce_openErr oe st q opv oeM s a args σ0 hpre hO hb he
    · exact ce_open41 oe st q opv oeM s a args σ0 hpre hO hb
  · by_cases hR : Model.aOp a = opReadK
    · cases hb : s.cust.isOpen
      · exact ce_read47 oe st q opv oeM s a args σ0 hpre hR hb
      · exact ce_readLoop oe st q opv oeM s a args σ0 hpre hR hb
    · by_cases hC : Model.aOp a = opClose
      · cases hb : s.cust.isOpen
        · exact ce_close42 oe st q opv oeM s a args σ0 hpre hC hb
        · exact ce_close00 oe st q opv oeM s a args σ0 hpre hC hb
      · exact ce_other oe st q opv oeM s a args σ0 hpre hO hR hC

end EquivLean.Modernize.Cbstm03b.Java.CustP

namespace EquivLean.Modernize.Cbstm03b.Java

open CustP in
/-- **`custProc`** (CUSTFILE) for fixed ghost values: the entry path and the paths from the two loop cut points, the
callees answered by their contracts (`custCalleesF`), the `FdCustfileRec` constructor inlined. -/
theorem custProc_vc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    MethodVC Gen.prog custCalleesF.env 1 custProcRef (procSpecG ddCust oe st q opv oeM s a)
      (custInvG st q s a) 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · have h := cust_entry oe st q opv oeM s a args σ0 hpre
    rw [custWP_def] at h
    exact h
  · intro p hp fr σ hA
    simp only [custInvG, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · have h := cust_seg49 oe st q opv oeM s a args σ0 hpre fr σ hA
      rw [custWP_def] at h
      exact h
    · have h := cust_seg53 oe st q opv oeM s a args σ0 hpre fr σ hA
      rw [custWP_def] at h
      exact h
    · have h := cust_seg80 oe st q opv oeM s a args σ0 hpre fr σ hA
      rw [custWP_def] at h
      exact h

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.custProc_vc
