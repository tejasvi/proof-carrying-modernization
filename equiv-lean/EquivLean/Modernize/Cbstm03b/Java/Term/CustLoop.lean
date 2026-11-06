import EquivLean.Modernize.Cbstm03b.Java.Term.CustDefs

/-!
# CBSTM03B → Java, termination of `custProc`: the paths from the loop head

From statement 49 with `custInvT`: past the last record (status 23), to the next record (back to statement 49,
`i5` one larger: the variant decreases), or the record found (the read). The record at `i5` is the entry state's
(`Keeps`, the FD record object not being a record of the file: `SepM`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java


set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000000 in
theorem cust_tloop (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) (args : List Value) (σ0 : State)
    (hpre : (kSpecT ddCust "custFile" "fdCustfileRec" oe st q opv oeM s a o1 y0).pre args σ0)
    (fr : Frame) (σ : State) (hJ : custInvT st q o1 y0 args σ0 fr σ) :
    custTWP [(49, fun fr' σ' => custInvT st q o1 y0 args σ0 fr' σ' ∧
      custVarT args σ0 fr' σ' < custVarT args σ0 fr σ)] 49 fr σ := by
  obtain ⟨⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩, ⟨fsS, hst, gfile, grec⟩⟩ := hpre
  obtain ⟨fs, hst', -, -, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, -⟩, -⟩ := stateAtM_iff.1 hS
  rw [hst] at hst'
  cases hst'
  rw [gfile] at g1
  cases g1
  rw [grec] at k1
  cases k1
  obtain ⟨o1', fs1, l, et, xs, hoo, ho1, hopen, hrecs, hl, hlen, hrecsF, -, -, -⟩ := m1
  cases hoo
  obtain ⟨y0', fsY, c0, d0, sc0, sd0, hyy, hy0, -, -, -, -, -, -, -⟩ := custRecAt_of j1 hV.2.2.2.2.2.2.1
  cases hyy
  obtain ⟨fsS', hstS, hsepC, -⟩ := hsep
  rw [hst] at hstS
  cases hstS
  have hny : Value.ref y0 ∉ xs := hsepC _ _ grec gfile o1 fs1 l et xs rfl ho1 hrecs hl
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨i, m, fsY', z, idS, f0, f1, f3, f6, f8, hm, hi0, hy0', gz, hz, hk, hinits⟩ := hJ
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
  have hlt_z := State.lt_next_of_heap hz
  have hxl : xs.length = s.cust.recs.length := Forall2.length_eq hrecsF
  rcases Int.lt_or_le i.toInt xs.length with hlt | hge
  · -- the record at `i5`
    have hk' : i.toInt.toNat < xs.length := by omega
    have hik : i.toNat = i.toInt.toNat := by
      have := BitVec.toInt_eq_toNat_cond i
      split at this <;> omega
    have hkr : i.toInt.toNat < s.cust.recs.length := by omega
    have hvr : Model.FdCustfileRec.Valid (s.cust.recs[i.toInt.toNat]'hkr) := hV.2.2.1 _ (List.getElem_mem hkr)
    have hjr := (Glue.forall2_iff.1 hrecsF).2 i.toInt.toNat hk'
    rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hkr] at hjr
    obtain ⟨xr, fsr, c, d, sc, sd, hxv, hxr, -, hc, hd, gc, jc, gd, jd⟩ := custRecAt_of hjr hvr
    obtain ⟨xsc, rfl, hxsc⟩ := jc
    obtain ⟨xsd, rfl, hxsd⟩ := jd
    have hxmem : Value.ref xr ∈ xs := by rw [← hxv]; exact List.getElem_mem hk'
    have hxry : xr ≠ y0 := fun e => hny (e ▸ hxmem)
    have hxr1 := keeps_heap hk hxr hxry
    have hxsc1 := keeps_heap hk hxsc (ne_of_str_plain hxsc hy0)
    have hxsd1 := keeps_heap hk hxsd (ne_of_str_plain hxsd hy0)
    have hxe : xs[i.toNat]? = some (.ref xr) := by rw [hik, List.getElem?_eq_getElem hk', hxv]
    have hxe' : xs[i.toInt.toNat]'hk' = .ref xr := hxv
    clear hjr hvr hrecsF hV hS hA hVa hK hE hopA hsepC hny hxmem hxr hxsc hxsd hst hq ho1 hl
    have hkK := Kept.intro hk
    simp only [custTWP]
    set_option jimple.modelContracts true in
      jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split, StrOk,
        cp037Str_length, argText, custInvT, custVarT]
    all_goals exact Kept.elim hkK
  · -- past the last record
    clear hrecsF hV hS hA hVa hK hE hopA hsepC hny hst hq ho1 hl
    simp only [custTWP]
    jvc [ite_nat_ne, custCalleesT, status2Sig, fitSig, keySubSig, spacesSig, grows_split, custInvT, custVarT]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.cust_tloop
