import EquivLean.Modernize.Cbstm03b.Java.Term.AcctDefs

/-!
# CBSTM03B → Java, termination of `acctProc`: the paths from the first loop head

From statement 33 with `acctInv33`: the next character of the key part (back to statement 33, `$i0` one larger), or
past the key part: the FD record's key written, then the closed file (status 47) or the second loop head
(statement 65, its variant below the first's).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000000 in
theorem acct_tdigit (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) (args : List Value) (σ0 : State)
    (hpre : (kSpecT ddAcct "acctFile" "fdAcctfileRec" oe st q opv oeM s a o1 y0).pre args σ0)
    (fr : Frame) (σ : State) (hJ : acctInv33 st q o1 y0 args σ0 fr σ) :
    acctTWP [(33, fun fr' σ' => acctInv33 st q o1 y0 args σ0 fr' σ' ∧
        acctVar33 args σ0 fr' σ' < acctVar33 args σ0 fr σ),
      (65, fun fr' σ' => acctInv65 st q o1 y0 args σ0 fr' σ' ∧
        acctVar65 args σ0 fr' σ' < acctVar33 args σ0 fr σ)] 33 fr σ := by
  obtain ⟨⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩, ⟨fsS, hst, gfile, grec⟩⟩ := hpre
  obtain ⟨fs, hst', -, -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩⟩ := stateAtM_iff.1 hS
  rw [hst] at hst'
  cases hst'
  rw [gfile] at g1
  cases g1
  rw [grec] at k1
  cases k1
  obtain ⟨o1', fs1, l, et, xs, hoo, ho1, hopen, hrecs, hl, hlen, -, -, -, -⟩ := m1
  cases hoo
  obtain ⟨y0', fsY, n0, d0, sd0, hyy, hy0, -, -, -, -, -, -, -⟩ := acctRecAt_of j1 hV.2.2.2.2.2.2.2.1
  cases hyy
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨i, v, xk, ks, f0, f3, f17, f8, f1, f11, hxk, hks, hi0, hy00, hk, hinits⟩ := hJ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hI
  have hys : y0 ≠ st := ne_of_cls hy0 hst (by decide)
  have hyq : y0 ≠ q := ne_of_cls hy0 hq (by decide)
  have hyo : y0 ≠ o1 := ne_of_cls hy0 ho1 (by decide)
  have hsq : st ≠ q := ne_of_cls hst hq (by decide)
  have hso : st ≠ o1 := ne_of_cls hst ho1 (by decide)
  have hqo : q ≠ o1 := ne_of_cls hq ho1 (by decide)
  have hyl : y0 ≠ l := fun e => by rw [e, hl] at hy0; cases hy0
  have hst1 := keeps_heap hk hst hys.symm
  have hq1 := keeps_heap hk hq hyq.symm
  have ho11 := keeps_heap hk ho1 hyo.symm
  have hl1 := keeps_heap hk hl hyl.symm
  have hy01 : σ.heap y0 = some (.plain "Cbstm03b$FdAcctfileRec" fsY) := by rw [hy00, hy0]
  have hlt_st := State.lt_next_of_heap hst1
  have hlt_q := State.lt_next_of_heap hq1
  have hlt_o1 := State.lt_next_of_heap ho11
  have hlt_y0 := State.lt_next_of_heap hy01
  have hlt_xk := State.lt_next_of_heap hxk
  have hkK := Kept.intro hk
  clear hV hS hA hVa hK hE hopA hsep hst hq ho1 hl hy00 hk j1
  cases hb : s.acct.isOpen
  · rw [hb] at hopen
    simp only [acctTWP]
    jvc [ite_nat_ne, acctCalleesT, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, grows_split, acctInv33,
      acctInv65, acctVar33, acctVar65]
    all_goals keepsK_tac
  · rw [hb] at hopen
    simp only [acctTWP]
    jvc [ite_nat_ne, acctCalleesT, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, grows_split, acctInv33,
      acctInv65, acctVar33, acctVar65]
    all_goals keepsK_tac

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.acct_tdigit
