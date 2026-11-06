import EquivLean.Modernize.Cbstm03b.Java.AcctSearch

/-!
# CBSTM03B → Java, `acctProc`: the search, record `j` (statement 65)

Record `j` does not match: on to `j + 1` (`J65`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → ∀ j (h1 : j < l1.length) (h2 : j < l2.length),
      R l1[j] l2[j]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ hs, j + 1, h1, h2 =>
    forall2_getElem hs j (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

/-- Record `j` of the file, as the search reads it. -/
theorem rec_at {σ0 : State} {o4 fdr l : Addr} {fs4 : List (FieldKey × Value)} {et : JType} {xs : List Value}
    {f : Model.FileM} (hrs : Forall2 (fun x vals => JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 x vals)
      xs f.recs)
    (hval : ∀ r ∈ f.recs, Model.FdAcctfileRec.Valid r) (hnr : NotRecOf σ0 "Cbstm03b$AcctFile" (.ref fdr) (.ref o4))
    (ho4 : σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4))
    (hrec4 : Fields.get fs4 ("Cbstm03b$AcctFile", "recs") = some (.ref l)) (hl : σ0.heap l = some (.array et xs))
    (j : Nat) (hj : j < f.recs.length) :
    ∃ (y : Addr) (fsy : List (FieldKey × Value)) (n : Int) (d : List UInt8) (sd : Value) (hjx : j < xs.length),
      xs[j] = .ref y ∧ σ0.heap y = some (.plain "Cbstm03b$FdAcctfileRec" fsy) ∧ f.recs[j] = [.num n, .str d] ∧
      0 ≤ n ∧ n < 100000000000 ∧ d.length = 289 ∧
      Fields.get fsy ("Cbstm03b$FdAcctfileRec", "fdAcctId") = some (.long (BitVec.ofInt 64 n)) ∧
      Fields.get fsy ("Cbstm03b$FdAcctfileRec", "fdAcctData") = some sd ∧ JStrAt σ0 sd (cp037Str d) ∧ y ≠ fdr := by
  have hjx : j < xs.length := by rw [forall2_length hrs]; exact hj
  obtain ⟨y, fsy, n, d, sd, ey, hy, hrj, hn0, hn1, hd, g1, g2, j2⟩ :=
    acctRecAt_of (forall2_getElem hrs j hjx hj) (hval _ (List.getElem_mem hj))
  refine ⟨y, fsy, n, d, sd, hjx, ey, hy, hrj, hn0, hn1, hd, g1, g2, j2, fun e => ?_⟩
  subst e
  exact hnr o4 fs4 l et xs rfl ho4 hrec4 hl (ey ▸ List.getElem_mem hjx)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_search_next {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (fr : Frame) (σ : State) (hJ : J65 oe st q s a σ0 fr σ)
    (hcase : ∀ j, fr.get 10 = some (.int (BitVec.ofNat 32 j)) → j ≤ s.acct.recs.length →
      j < s.acct.recs.length ∧ Model.numOf ((s.acct.recs.getD j []).getD 0 default) ≠ (keyVal a : Int)) :
    acctWP oe st q opv oeM s a σ0 65 fr σ := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  obtain ⟨hopK, hopen, ⟨f18, f17, f0, f3⟩, j', f8, f10, hj, hnm, hfd, hinit, hstat⟩ := hJ
  obtain ⟨hjl, hne⟩ := hcase j' f10 hj
  clear hcase
  obtain ⟨hkf, hfdr⟩ := hfd fs fdr fsr hst gr hr
  have hF' := hF
  unfold FinCtx at hF'
  obtain ⟨-, -, -, hV, -, -, -, -, -, -, -, mr, hnr, -, -, ha, -, -, lkey, -, -, -, -, -, -, -, -, -, -, -, -, -,
    n4, n5, n6, -, -, -, -, -, -⟩ := hF'
  obtain ⟨y, fsy, nj, dj, sdj, hjx, ey, hy, hrj, hnj0, hnj1, hdj, gyid, gydata, jyd, nyf⟩ :=
    rec_at hrs hV.2.2.2.1 hnr ho4 hrec4 hl j' hjl
  have hxl := forall2_length hrs
  have nlf : l ≠ fdr := fun e => by rw [e, hr] at hl; cases hl
  have f3' := f3 fs hst
  rw [g4] at f3'
  have hst1 : σ.heap st = some (.plain "Cbstm03b$State" fs) := by
    rw [hkf.2 st (State.lt_next_of_heap hst) n4.symm, hst]
  have ho41 : σ.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) := by
    rw [hkf.2 o4 (State.lt_next_of_heap ho4) n5.symm, ho4]
  have hl1 : σ.heap l = some (.array et xs) := by rw [hkf.2 l (State.lt_next_of_heap hl) nlf, hl]
  have hy1 : σ.heap y = some (.plain "Cbstm03b$FdAcctfileRec" fsy) := by
    rw [hkf.2 y (State.lt_next_of_heap hy) nyf, hy]
  have hI1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinit]; exact hI0
  have htj := toInt32_ofNat (n := j') (by omega)
  have htl := toInt32_ofNat (n := xs.length) hlen
  have hmodj : j' % 4294967296 = j' := Nat.mod_eq_of_lt (by omega)
  have hne' : nj ≠ (keyVal a : Int) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some, hrj] at hne
    simpa [Model.numOf] using hne
  have hkv : (BitVec.ofNat 64 (keyVal a)).toInt = (keyVal a : Int) := by
    have := jkey_lt (keyText a)
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    have e : keyVal a % 2 ^ 64 = keyVal a := Nat.mod_eq_of_lt (by unfold keyVal; omega)
    rw [e]
    split
    · rfl
    · unfold keyVal at *; omega
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  have n4' := n4.symm
  have n5' := n5.symm
  have n6' := n6.symm
  have hH := hid_intro (And.intro hst <| And.intro ho4 <| And.intro hr <| And.intro hq <| And.intro hinit <|
    And.intro hstat <| And.intro hkf <| And.intro hnm <| And.intro hxl <| And.intro hrj hne)
  clear hpre hrs f3 hst ho4 hr hq hl hI0 hxop hV mr ha lkey hopv hb hinit hstat hkf hfd hnm hxl hy jyd hrj hne hnr
  simp only [acctWP, procSpecG, Spec.of]
  have hne'' : nj ≠ (BitVec.ofNat 64 (keyVal a)).toInt := by rw [hkv]; exact hne'
  have hneBV : BitVec.ofInt 64 nj ≠ BitVec.ofNat 64 (keyVal a) := fun e => by
    apply hne''
    rw [← e, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofInt]
    simp only [Nat.reducePow, Nat.cast_ofNat]
    have e2 : nj % 18446744073709551616 = nj := Int.emod_eq_of_lt hnj0 (by omega)
    rw [e2]
    split <;> omega
  clear hkv
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3', n4, n5, n6, hneBV]
  all_goals obtain ⟨hst, ho4, hr, hq, hinit, hstat, hkf, hnm, hxl, hrj, hne⟩ := hid_elim hH
  all_goals
    unfold J65
    refine ⟨hopK, hopen, ⟨?_, ?_, ?_, fun fs' h => ?_⟩, j' + 1, ?_, ?_, by omega, fun i hi => ?_,
      fun fs' fdr' fsr' h1 h2 h3 => ?_, hinit, hstat⟩
    · simp [Frame.get_setLocal, f18]
    · simp [Frame.get_setLocal, f17]
    · simp [Frame.get_setLocal, f0]
    · rw [hst] at h; cases h; simp [Frame.get_setLocal, f3', g4]
    · simp [Frame.get_setLocal, f8]
    · rw [Frame.get_setLocal, if_pos rfl, ofNat_succ32]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact hnm i h
      · subst h; exact hne
    · rw [hst] at h1; cases h1; rw [gr] at h2; cases h2; rw [hr] at h3; cases h3; exact ⟨hkf, hfdr⟩

end EquivLean.Modernize.Cbstm03b.Java.AcctP
