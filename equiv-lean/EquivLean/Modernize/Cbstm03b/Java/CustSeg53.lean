import EquivLean.Modernize.Cbstm03b.Java.CustSeg

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

theorem ofNat_succ32' (i : Nat) : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

attribute [local irreducible] EquivLean.Cobol.Rec.JRecAt fixStr CardDemo.Cbstm03b.intoBuf
  EquivLean.Cobol.Rec.Schema.encode

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option jimple.modelContracts true in
theorem cust_seg53 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddCust oe st q opv oeM s a).pre args σ0) (fr : Frame) (σ : State)
    (hInv : Inv53 st q s a args σ0 fr σ) :
    custWP oe st q opv oeM s a args σ0 53 fr σ := by
  cust_destruct
  unfold Inv53 at hInv
  obtain ⟨fs', c, xr', k9, fsX', fsC', l', i, hst', hc', hxr', hxrh', hoc', hlc', hf0, hf1, hf3, hf6, hf8, hf13, hn,
    hfr, hxrσ, hk9, hinits, hi, hnm, hopK, hopen'⟩ := hInv
  rw [hst] at hst'
  cases hst'
  rw [g1] at hc'
  cases hc'
  rw [k1] at hxr'
  cases hxr'
  rw [hxr] at hxrh'
  cases hxrh'
  rw [ho1] at hoc'
  cases hoc'
  rw [hrecs] at hlc'
  cases hlc'
  -- record `i`: its object and its two strings, kept since the entry (it is not the FD record object)
  obtain ⟨hS0, hsep0, -, -, -, -, hrecsF, -, -, -, -, -, -⟩ := Kept.elim hkept
  have hil : i < xs.length := by omega
  obtain ⟨ri, hri⟩ : ∃ ri, s.cust.recs[i]? = some ri := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨xi, hxi⟩ : ∃ xi, xs[i]? = some xi := ⟨_, List.getElem?_eq_getElem hil⟩
  have hVr : Model.FdCustfileRec.Valid ri := hV.2.2.1 ri (List.mem_of_getElem? hri)
  obtain ⟨rx, fsr, rid, rdat, srid, srdat, rfl, hrx, hri', hridl, hrdatl, grid, jrid, grdat, jrdat⟩ :=
    custRecAt_of (forall2_get hrecsF hxi hri) hVr
  obtain ⟨xid, rfl, hxid⟩ := jrid
  obtain ⟨xdat, rfl, hxdat⟩ := jrdat
  have hrxx : rx ≠ xr := ne_xr_of_mem (nr_of_sep hsep0 hst g1 k1) ho1 hrecs hl (List.mem_of_getElem? hxi)
  have hlt_rx := State.lt_next_of_heap hrx
  have hlt_id := State.lt_next_of_heap hxid
  have hlt_dat := State.lt_next_of_heap hxdat
  have hrxσ : σ.heap rx = some (.plain "Cbstm03b$FdCustfileRec" fsr) := by rw [hfr rx hlt_rx hrxx]; exact hrx
  have hidσ : σ.heap xid = some (.str (cp037Str rid)) := by
    rw [hfr xid hlt_id (ne_of_heap hxid hxr (by intro h; cases h))]; exact hxid
  have hdatσ : σ.heap xdat = some (.str (cp037Str rdat)) := by
    rw [hfr xdat hlt_dat (ne_of_heap hxdat hxr (by intro h; cases h))]; exact hxdat
  have hxi' : xs[(BitVec.ofNat 32 i).toNat]? = some (.ref rx) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hxi
  have hxi'' : xs[i % 4294967296]? = some (.ref rx) := by rw [Nat.mod_eq_of_lt (by omega)]; exact hxi
  obtain ⟨_, hxi3⟩ := List.getElem?_eq_some_iff.1 hxi
  have hidl : (cp037Str rid).length < 2147483648 := by rw [cp037Str_length]; omega
  have hdatl : (cp037Str rdat).length < 2147483648 := by rw [cp037Str_length]; omega
  have e : s.cust.recs.getD i [] = ri := by rw [List.getD_eq_getElem?_getD, hri, Option.getD_some]
  have hkept7 := Kept.intro (And.intro hi (And.intro e (And.intro hri' (And.intro hridl (And.intro hrdatl
    (And.intro hrxx (And.intro hrx (And.intro hxid (And.intro hxdat (And.intro grid grdat))))))))))
  clear hS0 hsep0 hrecsF
  cust_loop_facts
  by_cases hm : rid = key9 a
  · have hf : s.cust.recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key9 a) = some i := by
      obtain ⟨-, hnm, -⟩ := Kept.elim hkept2
      refine findIdx_some hnm hi ?_
      rw [e, hri']
      exact hm
    have hm' : cp037Str (key9 a) = cp037Str rid := by rw [hm]
    have hid_s : xid ≠ st := ne_of_heap hxid hst (by intro h; cases h)
    have hid_q : xid ≠ q := ne_of_heap hxid hq (by intro h; cases h)
    have hid_o : xid ≠ o1 := ne_of_heap hxid ho1 (by intro h; cases h)
    have hdat_s : xdat ≠ st := ne_of_heap hxdat hst (by intro h; cases h)
    have hdat_q : xdat ≠ q := ne_of_heap hxdat hq (by intro h; cases h)
    have hdat_o : xdat ≠ o1 := ne_of_heap hxdat ho1 (by intro h; cases h)
    have hkept9 := Kept.intro hf
    simp only [custWP_def]
    clear e hri' hf hri
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_loop_kept
    all_goals obtain ⟨hi', e', hri'', hridl', hrdatl', hrxx', hrx', hxid', hxdat', grid', grdat'⟩ := Kept.elim hkept7
    all_goals have hf' := Kept.elim hkept9
    delta Inv80
    refine ⟨_, _, _, _, o1, xr, rx, σ.next + 1, σ.next, xid, xdat, i, _, _, hst, g1, k1, ho1, hq, hrx', grid', grdat',
      hxid', hxdat', hrxx', hridl', hrdatl', e'.trans hri'', hi', hf', hopK', hopen'',
      by simp only [Frame.get_setLocal]; exact hf0', by simp only [Frame.get_setLocal]; exact hf3',
      by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte],
      by simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte],
      hn', Nat.lt_succ_self _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.next_setObj, State.next_alloc]
      exact Nat.lt_succ_self _
    · intro y hy h1 h2 h3
      chsimp
      exact hfr y hy h1
    · chsimp
    · chsimp
    · chsimp
      rfl
    · chsimp
    · simp only [State.setObj_inits, State.alloc_inits]
      exact hinits'
  · have hmn : Model.strOf ((s.cust.recs.getD i []).getD 0 default) ≠ key9 a := by
      rw [e, hri']
      exact hm
    have hkept8 := Kept.intro hmn
    have hm' : ¬ (cp037Str (key9 a) = cp037Str rid) := fun h => hm (cp037Str_inj h).symm
    have hm'' : ¬ (cp037Str rid = cp037Str (key9 a)) := fun h => hm (cp037Str_inj h)
    simp only [custWP_def]
    jvc [ite_nat_ne, custInvG, custCalleesF, Contracts.env, status2Sig, fitSig, keySubSig, spacesSig, grows_split]
    all_goals cust_loop_kept
    all_goals obtain ⟨hi', -⟩ := Kept.elim hkept7
    all_goals have hmn' := Kept.elim hkept8
    unfold Inv49
    refine ⟨fs, o1, xr, k9, fsx, i + 1, hst, g1, k1, hxr, ?_, ?_, ?_, ?_, ?_, hn',
      hfr, hxrσ', hk9', hinits', hi', noMatch_succ hnm hmn', hopK', hopen''⟩
    · simp only [Frame.get_setLocal, ↓reduceIte]
      exact hf0'
    · simp only [Frame.get_setLocal, ↓reduceIte]
      exact hf1'
    · simp only [Frame.get_setLocal, ↓reduceIte]
      exact hf3'
    · simp only [Frame.get_setLocal, ↓reduceIte]
      exact hf6'
    · simp only [Frame.get_setLocal, ↓reduceIte, ofNat_succ32']

end EquivLean.Modernize.Cbstm03b.Java.CustP
