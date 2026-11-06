import EquivLean.Modernize.Cbstm03b.Java.Term.CustDefs

/-!
# CBSTM03B → Java, termination of `custProc`: the entry paths

From statement 0 to the end or to the loop head (statement 49), split as `trnx_tentry` (the operation, the file's
flag, the OPEN outcome). At the loop head, what `jvc` leaves is the heap kept but at `y0` (`keepsK_tac`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000000 in
theorem cust_tentry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) (args : List Value) (σ0 : State)
    (hpre : (kSpecT ddCust "custFile" "fdCustfileRec" oe st q opv oeM s a o1 y0).pre args σ0) :
    custTWP [(49, custInvT st q o1 y0 args σ0)] 0 (Frame.init true args) σ0 := by
  obtain ⟨⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩, ⟨fsS, hst, gfile, grec⟩⟩ := hpre
  obtain ⟨fs, hst', -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩, -⟩ := stateAtM_iff.1 hS
  rw [hst] at hst'
  cases hst'
  rw [gfile] at g1
  cases g1
  rw [grec] at k1
  cases k1
  obtain ⟨o1', fs1, l, et, xs, hoo, ho1, hopen, hrecs, hl, hlen, -, -, -, -⟩ := m1
  cases hoo
  obtain ⟨y0', fsY, c0, d0, sc0, sd0, hyy, hy0, -, -, -, -, -, -, -⟩ := custRecAt_of j1 hV.2.2.2.2.2.2.1
  cases hyy
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, -, -, hol, -, hkeyl, hkl1, hkl2,
    -, -, -, gop, jop, -, -, gkey, jkey, gkl, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨fsq0, hq0, hopv⟩ := hopA
  rw [hq] at hq0
  cases hq0
  rw [gop] at hopv
  cases hopv
  obtain ⟨xop, rfl, hxop⟩ := jop
  obtain ⟨xkey, rfl, hxkey⟩ := jkey
  have hkeyl' : (cp037Str key).length = 25 := by rw [cp037Str_length]; exact hkeyl
  obtain ⟨b, rfl⟩ : ∃ b, op = [b] := by
    match op, hol with
    | [b], _ => exact ⟨b, rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hI
  have hsq : st ≠ q := ne_of_cls hst hq (by decide)
  have hso : st ≠ o1 := ne_of_cls hst ho1 (by decide)
  have hqo : q ≠ o1 := ne_of_cls hq ho1 (by decide)
  have hys : y0 ≠ st := ne_of_cls hy0 hst (by decide)
  have hyq : y0 ≠ q := ne_of_cls hy0 hq (by decide)
  have hyo : y0 ≠ o1 := ne_of_cls hy0 ho1 (by decide)
  have hlt_st := State.lt_next_of_heap hst
  have hlt_q := State.lt_next_of_heap hq
  have hlt_o1 := State.lt_next_of_heap ho1
  have hlt_y0 := State.lt_next_of_heap hy0
  have hlt_key := State.lt_next_of_heap hxkey
  clear hS hA hsep hK hV j1 hVa hdd hkeyl
  by_cases hbO : b = opOpen
  · subst hbO
    rw [op_texts.1] at hxop
    cases hb : s.cust.isOpen
    · rw [hb] at hopen
      obtain ⟨eta, ys, hoe, hys, hysv⟩ := hE
      obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, ys = [e0, e1, e2, e3] := by
        match ys, hys with
        | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
      rcases hysv 2 (by decide) with ⟨he2, hoe2⟩ | ⟨ob, c, he2, hob, hc, hoe2⟩
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at he2
        subst he2
        simp only [custTWP]
        jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at he2
        subst he2
        simp only [custTWP]
        jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    · rw [hb] at hopen
      simp only [custTWP]
      jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
  · by_cases hbK : b = opReadK
    · subst hbK
      rw [op_texts.2.2.1] at hxop
      clear hE hol
      cases hb : s.cust.isOpen
      · rw [hb] at hopen
        simp only [custTWP]
        jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split, StrOk,
          cp037Str_length, argText, custInvT]
      · rw [hb] at hopen
        simp only [custTWP]
        jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split, StrOk,
          cp037Str_length, argText, custInvT]
        all_goals keepsK_tac
    · by_cases hbC : b = opClose
      · subst hbC
        rw [op_texts.2.2.2] at hxop
        cases hb : s.cust.isOpen
        · rw [hb] at hopen
          simp only [custTWP]
          jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
        · rw [hb] at hopen
          simp only [custTWP]
          jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
      · have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := by rw [← op_texts.1]; exact op_ne_text hbO
        have hnK : ¬ (cp037Str [b] = JStr.ofString "K") := by rw [← op_texts.2.2.1]; exact op_ne_text hbK
        have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := by rw [← op_texts.2.2.2]; exact op_ne_text hbC
        simp only [custTWP]
        jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.cust_tentry
