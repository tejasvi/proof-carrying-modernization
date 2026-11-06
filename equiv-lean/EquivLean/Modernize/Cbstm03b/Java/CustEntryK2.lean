import EquivLean.Modernize.Cbstm03b.Java.CustMac

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem ce_readLoop (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hR : Model.aOp a = opReadK)
    (hb : s.cust.isOpen = true) :
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
  have hkept3 : Kept (Model.aOp a = opReadK ∧ s.cust.isOpen = true) := Kept.intro ⟨hR, hb⟩
  simp only [custWP_def]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  · exact Or.inr ⟨_, _, rfl, by assumption, hkeyL⟩
  all_goals cust_k9
  cust_kept
  obtain ⟨hR', hb'⟩ := Kept.elim hkept3
  unfold Inv49
  refine ⟨fs, o1, xr, w, fsx, 0, hst, g1, k1, hxr, by cframe, by cframe, by cframe, by cframe, by cframe, ?_, ?_,
    ?_, ?_, ?_, Nat.zero_le _, noMatch_zero, hR', hb'⟩
  · simp only [State.next_setObj]
    exact Nat.le_trans (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
      (Nat.le_trans (by assumption) (by assumption))
  · intro y hy hne
    refine (show Keeps (fun z => z = xr) σ0 _ from ?_).2 y hy hne
    repeat (first | exact keeps_refl _ _ | (refine keeps_setObj' ?_ rfl) | (refine keeps_alloc' ?_) |
      (refine keeps_grows' ?_ (growsK_elim (by assumption))))
  · chsimp
  · chsimp
    refine (‹_ = some (Obj.str (fixStr _ 9))›).trans ?_
    rw [argText_ref ‹_ = some (Obj.str (cp037Str (List.take _ _)))›]
    rw [ha] at hkey9
    rw [ha, hkey9]
  · simp only [State.setObj_inits]
    assumption

end EquivLean.Modernize.Cbstm03b.Java.CustP
