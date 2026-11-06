import EquivLean.Modernize.Cbstm03b.Java.CustMac

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_open00 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a = opOpen)
    (hb : s.cust.isOpen = false) (he : oeM 3 = none) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opOpen := hop.symm.trans hO
  rw [op_texts.1] at hxop
  clear hA' ha
  rw [hb] at hopen
  obtain ⟨eta, ys, hoe, hys, hysv⟩ := hE
  obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, ys = [e0, e1, e2, e3] := by
    match ys, hys with
    | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
  rcases hysv 2 (by decide) with ⟨he2, -⟩ | ⟨ob, c, -, -, -, hoe2⟩
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at he2
    subst he2
    simp only [custWP_def, procSpecG, Spec.of, callC_open00 hdd hop hb he]
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_kept
    · cS_state
    · cS_sep
    · cS_area
  · rw [he] at hoe2
    cases hoe2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_openErr (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a = opOpen)
    (hb : s.cust.isOpen = false) {c0 : Nat} (he : oeM 3 = some c0) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opOpen := hop.symm.trans hO
  rw [op_texts.1] at hxop
  clear hA' ha
  rw [hb] at hopen
  obtain ⟨eta, ys, hoe, hys, hysv⟩ := hE
  obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, ys = [e0, e1, e2, e3] := by
    match ys, hys with
    | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
  rcases hysv 2 (by decide) with ⟨-, hoe2⟩ | ⟨ob, c, he2, hob, hc, hoe2⟩
  · rw [he] at hoe2
    cases hoe2
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at he2
    subst he2
    rw [he] at hoe2
    cases hoe2
    simp only [custWP_def, procSpecG, Spec.of, callC_openErr hdd hop hb he]
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_kept
    · cG_state
    · cG_sep
    · cG_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_open41 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a = opOpen)
    (hb : s.cust.isOpen = true) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opOpen := hop.symm.trans hO
  rw [op_texts.1] at hxop
  clear hA' ha hE
  rw [hb] at hopen
  simp only [custWP_def, procSpecG, Spec.of, callC_open41 hdd hop hb]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  all_goals cust_kept
  · cS_state
  · cS_sep
  · cS_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_close42 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hC : Model.aOp a = opClose)
    (hb : s.cust.isOpen = false) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opClose := hop.symm.trans hC
  rw [op_texts.2.2.2] at hxop
  clear hA' ha hE
  rw [hb] at hopen
  simp only [custWP_def, procSpecG, Spec.of, callC_close42 hdd hop hb]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  all_goals cust_kept
  · cS_state
  · cS_sep
  · cS_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_close00 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hC : Model.aOp a = opClose)
    (hb : s.cust.isOpen = true) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  obtain rfl : b = opClose := hop.symm.trans hC
  rw [op_texts.2.2.2] at hxop
  clear hA' ha hE
  rw [hb] at hopen
  simp only [custWP_def, procSpecG, Spec.of, callC_close00 hdd hop hb]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  all_goals cust_kept
  · cS_state
  · cS_sep
  · cS_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
theorem ce_other (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a ≠ opOpen)
    (hKo : Model.aOp a ≠ opReadK) (hC : Model.aOp a ≠ opClose) :
    custWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  cust_destruct
  have hbO : b ≠ opOpen := hop ▸ hO
  have hbK : b ≠ opReadK := hop ▸ hKo
  have hbC : b ≠ opClose := hop ▸ hC
  have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := fun h =>
    hbO (List.cons.inj (cp037Str_inj (h.trans op_texts.1.symm))).1
  have hnK : ¬ (cp037Str [b] = JStr.ofString "K") := fun h =>
    hbK (List.cons.inj (cp037Str_inj (h.trans op_texts.2.2.1.symm))).1
  have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := fun h =>
    hbC (List.cons.inj (cp037Str_inj (h.trans op_texts.2.2.2.symm))).1
  clear hA' ha hE
  simp only [custWP_def, procSpecG, Spec.of, callC_other hdd hO hKo hC]
  jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  all_goals cust_kept
  all_goals have hzq : zs ≠ q := ne_of_heap hzs hq (by intro h; cases h)
  · exact (finC_ex (f' := s.cust) (r' := s.custRec) (c' := s.custSt) hS hst (by keeps4_tac)
      (away4 hst hq ho1 hxr (by decide)) ⟨fs, by chsimp; exact hst, fun k _ _ => rfl,
        ⟨_, g1, fileC_same m1 ho1 (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))
          (rec4 hst hq ho1 (nr_of_sep hsep hst g1 k1)) (by chsimp)⟩,
        ⟨_, k1, jRecAt_same j1 (by chsimp) (by keeps4_tac) (away4 hst hq ho1 hxr (by decide))⟩,
        ⟨_, n1, zs, rfl, by chsimp; exact hzs⟩⟩)
  · exact sepC hS hsep hst (by keeps4_tac) (away4 hst hq ho1 hxr (by decide)) (by chsimp; exact hst) rfl rfl
      (fun x y hx hy => by
        rw [k1] at hx
        rw [g1] at hy
        cases hx
        cases hy
        exact notRecOf_tr ho1 (by chsimp; exact ho1) rfl hrecs (by chsimp) (nr_of_sep hsep hst g1 k1))
  · exact area_rc hA hVa hq (by keeps4_tac) (away4 (cs := []) hst hq ho1 hxr (by decide)) (by chsimp; try rfl)
      (fun k h => get_set_other h) get_set_same ⟨zs, rfl, by chsimp; exact hzs⟩

end EquivLean.Modernize.Cbstm03b.Java.CustP
