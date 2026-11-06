import EquivLean.Modernize.Cbstm03b.Java.AcctPre

/-!
# CBSTM03B → Java, `acctProc`: the search (statement 65)

The first record whose `fdAcctId` is the key value: status `00`, the record into the FD record object (a fresh
copy) and into `LK-M03B-FLDT`; none: status `23`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

theorem keeps_mono {A B : Addr → Prop} {σ σ' : State} (h : ∀ y, A y → B y) (hk : Keeps A σ σ') :
    Keeps B σ σ' :=
  ⟨hk.1, fun y hy hB => hk.2 y hy (fun hA => hB (h y hA))⟩

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hs => by simp [forall2_length hs]

theorem call_key_none {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opReadK) (ho : s.acct.isOpen = true)
    (hnone : ∀ i, i < s.acct.recs.length → Model.numOf ((s.acct.recs.getD i []).getD 0 default) ≠
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat) :
    Model.call oeM s a =
      ({ s with
          acct := s.acct
          acctRec := s.acctRec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat))
          acctSt := Model.stCp 23 }, Model.setRc a (stBytes 23)) := by
  have hf : s.acct.recs.findIdx? (fun x => Model.numOf (x.getD 0 default) ==
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hnone i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    simp only [beq_eq_false_iff_ne]
    exact this
  rw [call_acct hdd, hop]
  simp only [Model.keyStep, Model.keyReadM]
  rw [hf]
  simp [ho, show opReadK ≠ opOpen by decide]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_search_none {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (fr : Frame) (σ : State) (hJ : J65 oe st q s a σ0 fr σ) (hjl : ∀ j, fr.get 10 = some (.int (BitVec.ofNat 32 j)) →
      s.acct.recs.length ≤ j) :
    acctWP oe st q opv oeM s a σ0 65 fr σ := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  obtain ⟨hopK, hopen, ⟨f18, f17, f0, f3⟩, j, f8, f10, hj, hnm, hfd, hinit, hstat⟩ := hJ
  have hjl' := hjl j f10
  obtain ⟨hkf, hfdr⟩ := hfd fs fdr fsr hst gr hr
  have hF' := hF
  unfold FinCtx at hF'
  obtain ⟨-, -, -, hV, -, -, -, -, -, -, -, mr, -, -, -, ha, -, -, lkey, -, -, -, -, -, -, -, -, -, -, -, -, -,
    n4, n5, n6, -, -, -, -, -, -⟩ := hF'
  obtain ⟨xr, fsr', n0, d0, sd0, exr, hxr, hrec0, hn0, hn1, hd0, gid, gdata, jdata⟩ :=
    acctRecAt_of mr hV.2.2.2.2.2.2.2.1
  cases exr
  rw [hr] at hxr
  cases hxr
  have hxl := forall2_length hrs
  have nlf : l ≠ fdr := fun e => by rw [e, hr] at hl; cases hl
  have f3' := f3 fs hst
  rw [g4] at f3'
  have hst1 : σ.heap st = some (.plain "Cbstm03b$State" fs) := by
    rw [hkf.2 st (State.lt_next_of_heap hst) n4.symm, hst]
  have ho41 : σ.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) := by
    rw [hkf.2 o4 (State.lt_next_of_heap ho4) n5.symm, ho4]
  have hq1 : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by
    rw [hkf.2 q (State.lt_next_of_heap hq) n6.symm, hq]
  have hl1 : σ.heap l = some (.array et xs) := by rw [hkf.2 l (State.lt_next_of_heap hl) nlf, hl]
  have hI1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinit]; exact hI0
  have hjx : j = xs.length := by omega
  subst hjx
  have htj := toInt32_ofNat (n := xs.length) hlen
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  have n4' := n4.symm
  have n5' := n5.symm
  have n6' := n6.symm
  have hH := hid_intro (And.intro hst <| And.intro ho4 <| And.intro hr <| And.intro hq <| And.intro hinit <|
    And.intro hstat <| And.intro hrec0 <| And.intro jdata <| And.intro hkf <| And.intro hnm hxl)
  clear hpre hrs f3 hst ho4 hr hq hl hI0 hxop hV mr hrec0 hn0 hn1 hd0 jdata ha lkey hopv hb hinit hstat hkf
    hfd hnm hjl hjl' hj hxl
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3', n4, n5, n6, n4', n5', n6']
  all_goals obtain ⟨hst, ho4, hr, hq, hinit, hstat, hrec0, jdata, hkf, hnm, hxl⟩ := hid_elim hH
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  all_goals have hk1 : Keeps (AccA st o4 q fdr) σ0 σ := keeps_mono (fun y h => Or.inr (Or.inr (Or.inr h))) hkf
  all_goals have hval := acctVal_keyVal hK hopK hdd ha lkey
  all_goals have hnone : ∀ i, i < s.acct.recs.length → Model.numOf ((s.acct.recs.getD i []).getD 0 default) ≠
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat := fun i hi => by rw [hval]; exact hnm i (by omega)
  · rw [call_key_none hdd hopK hopen hnone]
    refine state_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
      hS hst ho4 hq hr ?hk ?hst ?hrest ⟨⟨.ref o4, ?g4, ?m4⟩, ⟨.ref fdr, ?gr, ?mr⟩, ⟨.ref σ.next, ?gs, ?js⟩⟩
    case hk => keeps_tac
    case hst => hsimp [n2, hst1]
    case hrest => exact fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2)
    case g4 => rw [get_set_ne _ (by decide +kernel)]; exact g4
    case gr => rw [get_set_ne _ (by decide +kernel)]; exact gr
    case mr =>
      rw [hrec0]
      refine acctRecAt_mk (fs := Fields.set fsr ("Cbstm03b$FdAcctfileRec", "fdAcctId")
          (.long (BitVec.ofNat 64 (keyVal a)))) ?_ ?_
        (by rw [get_set_ne _ (by decide +kernel)]; exact gdata) (jstrAt_keeps (by keeps_tac) haw0 jdata)
      · hsimp [n4, n6, hfdr]
      · rw [get_set_eq, hval, BitVec.ofInt_natCast]
    case gs => exact get_set_eq _ _ _
    case js => rw [status_text, ← lit_texts.2.2.2.2]; exact ⟨_, rfl, by hsimp⟩
    case m4 =>
      refine acctFile_fin (fs4' := fs4) m4 hnr hst ho4 hq hr ?_ ?_ rfl hop4 hpos heof rfl hp
      · keeps_tac
      · hsimp [n1', n3, ho41]
  · refine sepM_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
      (fs4' := fs4) (fdr' := fdr)
      hS hSep hst ho4 hq hr g4 gr ?hk ?hst (fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2))
      (by rw [get_set_ne _ (by decide +kernel)]; exact g4) (by rw [get_set_ne _ (by decide +kernel)]; exact gr)
      (Or.inl rfl) ?h4 rfl
    case hk => keeps_tac
    case hst => hsimp [n2, hst1]
    case h4 => hsimp [n1', n3, ho41]
  · rw [call_key_none hdd hopK hopen hnone, ha]
    refine area_fin (rc' := stBytes 23) (fldt' := fldt) (src' := .ref σ.next) (sfl' := sfl)
      (fsq' := Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref σ.next))
      ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
      (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel))
      (get_set_ne _ (by decide +kernel)) (get_set_eq _ _ _) ?j3
      (by rw [get_set_ne _ (by decide +kernel)]; exact g6) (jstrAt_keeps ?hk2 haw0 j6)
    case hk => keeps_tac
    case hq => hsimp
    case j3 => rw [stBytes_text, ← lit_texts.2.2.2.2]; exact ⟨_, rfl, by hsimp⟩
    case hk2 => keeps_tac

end EquivLean.Modernize.Cbstm03b.Java.AcctP
