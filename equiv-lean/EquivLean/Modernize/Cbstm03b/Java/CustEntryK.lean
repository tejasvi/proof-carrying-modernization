import EquivLean.Modernize.Cbstm03b.Java.CustMac

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
set_option jimple.modelContracts true in
theorem ce_read47 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hR : Model.aOp a = opReadK)
    (hb : s.cust.isOpen = false) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opReadK := hop.symm.trans hR
  rw [op_texts.2.2.1] at hxop
  have hAk : JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea"
      ((σ0.alloc (Obj.str (JStr.ofString "O"))).2.alloc (Obj.str (JStr.ofString "K"))).2 (.ref q) a :=
    jRecAt_grows hA' (grows_trans (grows_alloc _ _) (grows_alloc _ _))
  have hkey := hK.1 hop (Or.inl hdd)
  have hkeyL : (cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat)).length < 2147483648 := by
    rw [cp037Str_length, List.length_take]; omega
  have hkey9 : fixStr (cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat)) 9 = cp037Str (key9 a) :=
    fit_key9 (by rw [ha]; exact hkl) hkey.1 hkey.2
  clear hA' ha hE
  rw [hb] at hopen
  simp only [custWP_def, procSpecG, Spec.of, callC_read47 hdd hop hb]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  · exact Or.inr ⟨_, _, rfl, by assumption, hkeyL⟩
  all_goals cust_kept
  all_goals cust_k9
  · cK_state
  · cK_sep
  · cK_area

end EquivLean.Modernize.Cbstm03b.Java.CustP
