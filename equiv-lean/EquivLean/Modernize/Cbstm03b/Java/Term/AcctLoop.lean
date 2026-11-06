import EquivLean.Modernize.Cbstm03b.Java.Term.AcctDefs

/-!
# CBSTM03B → Java, termination of `acctProc`: the paths from the second loop head

From statement 65 with `acctInv65`: past the last record (status 23), to the next record (back to statement 65,
`i18` one larger), or the record found (the read: `zeroPad` of its key, whose value is not negative). The record
at `i18` is the entry state's (`Keeps`, the FD record object not being a record of the file: `SepM`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

theorem toInt_ofInt64_small {n : Int} (h0 : 0 ≤ n) (h1 : n < 100000000000) : (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> simp only [Nat.reducePow] <;> omega


set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000000 in
theorem acct_tloop (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) (args : List Value) (σ0 : State)
    (hpre : (kSpecT ddAcct "acctFile" "fdAcctfileRec" oe st q opv oeM s a o1 y0).pre args σ0)
    (fr : Frame) (σ : State) (hJ : acctInv65 st q o1 y0 args σ0 fr σ) :
    acctTWP [(33, fun fr' σ' => acctInv33 st q o1 y0 args σ0 fr' σ' ∧
        acctVar33 args σ0 fr' σ' < acctVar65 args σ0 fr σ),
      (65, fun fr' σ' => acctInv65 st q o1 y0 args σ0 fr' σ' ∧
        acctVar65 args σ0 fr' σ' < acctVar65 args σ0 fr σ)] 65 fr σ := by
  obtain ⟨⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩, ⟨fsS, hst, gfile, grec⟩⟩ := hpre
  obtain ⟨fs, hst', -, -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩⟩ := stateAtM_iff.1 hS
  rw [hst] at hst'
  cases hst'
  rw [gfile] at g1
  cases g1
  rw [grec] at k1
  cases k1
  obtain ⟨o1', fs1, l, et, xs, hoo, ho1, hopen, hrecs, hl, hlen, hrecsF, -, -, -⟩ := m1
  cases hoo
  obtain ⟨y0', fsY, n0, d0, sd0, hyy, hy0, -, -, -, -, -, -, -⟩ := acctRecAt_of j1 hV.2.2.2.2.2.2.2.1
  cases hyy
  obtain ⟨fsS', hstS, -, hsepA⟩ := hsep
  rw [hst] at hstS
  cases hstS
  have hny : Value.ref y0 ∉ xs := hsepA _ _ grec gfile o1 fs1 l et xs rfl ho1 hrecs hl
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨i, m, fsY', v, f0, f3, f17, f8, f10, hm, hi0, hy0', gv, hk, hinits⟩ := hJ
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
  have hlt_st := State.lt_next_of_heap hst1
  have hlt_q := State.lt_next_of_heap hq1
  have hlt_o1 := State.lt_next_of_heap ho11
  have hlt_y0 := State.lt_next_of_heap hy0'
  have hxl : xs.length = s.acct.recs.length := Forall2.length_eq hrecsF
  have hkK := Kept.intro hk
  rcases Int.lt_or_le i.toInt xs.length with hlt | hge
  · -- the record at `i18`
    have hk' : i.toInt.toNat < xs.length := by omega
    have hik : i.toNat = i.toInt.toNat := by
      have := BitVec.toInt_eq_toNat_cond i
      split at this <;> omega
    have hkr : i.toInt.toNat < s.acct.recs.length := by omega
    have hvr : Model.FdAcctfileRec.Valid (s.acct.recs[i.toInt.toNat]'hkr) := hV.2.2.2.1 _ (List.getElem_mem hkr)
    have hjr := (Glue.forall2_iff.1 hrecsF).2 i.toInt.toNat hk'
    rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hkr] at hjr
    obtain ⟨xr, fsr, n, d, sd, hxv, hxr, -, hn0, hn1, hd, gn, gd, jd⟩ := acctRecAt_of hjr hvr
    obtain ⟨xsd, rfl, hxsd⟩ := jd
    have hxmem : Value.ref xr ∈ xs := by rw [← hxv]; exact List.getElem_mem hk'
    have hxry : xr ≠ y0 := fun e => hny (e ▸ hxmem)
    have hxr1 := keeps_heap hk hxr hxry
    have hxsd1 := keeps_heap hk hxsd (ne_of_str_plain hxsd hy0)
    have hxe : xs[i.toNat]? = some (.ref xr) := by rw [hik, List.getElem?_eq_getElem hk', hxv]
    have hxe' : xs[i.toInt.toNat]'hk' = .ref xr := hxv
    have hn64 : (BitVec.ofInt 64 n).toInt = n := toInt_ofInt64_small hn0 hn1
    clear hjr hvr hrecsF hV hS hA hVa hK hE hopA hsepA hny hxmem hxr hxsd hst hq ho1 hl hk
    simp only [acctTWP]
    set_option jimple.modelContracts true in
      jvc [ite_nat_ne, acctCalleesT, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, grows_split, StrOk,
        cp037Str_length, argText, zpadStr_length, acctInv33, acctInv65, acctVar33, acctVar65]
    all_goals keepsK_tac
  · -- past the last record
    clear hrecsF hV hS hA hVa hK hE hopA hsepA hny hst hq ho1 hl hk
    simp only [acctTWP]
    jvc [ite_nat_ne, acctCalleesT, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, grows_split, acctInv33,
      acctInv65, acctVar33, acctVar65]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.acct_tloop
