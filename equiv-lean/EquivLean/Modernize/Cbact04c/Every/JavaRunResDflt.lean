import EquivLean.Modernize.Cbact04c.Every.JavaRunResAbend

/-!
# CBACT04C → Java, `run`: the `DEFAULT` disclosure group (statements 180–195)

When the account's group has no disclosure record for the category record, `run` displays the two
retry lines (cut point 184, `J184`) and looks up the group `DEFAULT   `: its record gives the rate
(cut point 196), or the run abends.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- Statement 184: the account's group had no record; the two retry lines are displayed. -/
def J184 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value) (ts : Addr),
    Body g fr σ i h tcbV ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (sel g i.toInt.toNat).total)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (sel g i.toInt.toNat).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    fr.get 28 = some (.ref ts) ∧
    σ.heap ts = some (.str (cp037Str (Model.tType (g.trec i.toInt.toNat)))) ∧
    fr.get 11 = some (.long (BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)))) ∧
    Hide (LoopHeap g σ0 σ h (sel g i.toInt.toNat) acctV xrefV lastV) ∧
    grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat) =
      true

theorem discIdx_none {σ : State} {a gs ts : Addr} {et : JType} {xs : List Value}
    {ds : List (List FV)} {grp ty : List UInt8} {cat : Int}
    (ha : σ.heap a = some (.array et xs)) (hgs : σ.heap gs = some (.str (cp037Str grp)))
    (hts : σ.heap ts = some (.str (cp037Str ty)))
    (h : Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs ds)
    (hv : ∀ d ∈ ds, DisGroupRecord.Valid d) (hc0 : 0 ≤ cat) (hc1 : cat < 10000)
    (hjd : ds.findIdx? (fun d => Model.dGrp d == grp && Model.dType d == ty && Model.dCat d == cat) =
      none) :
    discIdx σ a gs ts (BitVec.ofInt 64 cat) = -1 := by
  simp only [discIdx, ha, hgs, hts, findIdx_disc grp ty hc0 hc1 h hv, hjd]

/-- The cut at 184: the two retry lines added to the display list (statements 180–183). -/
theorem j184_of {g : G} {σ0 σ : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {ts : Addr} {dxs : List Value} {dm : Nat} {s1 s2 : JStr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hstop : (g.stE i.toInt.toNat).stop = false) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total)))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f28 : fr'.get 28 = some (.ref ts))
    (hts : σ.heap ts = some (.str (cp037Str (Model.tType (g.trec i.toInt.toNat)))))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)))))
    (hheap : Hide (LoopHeap g σ0 σ hp (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      acctV xrefV lastV))
    (hm : grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat) = true)
    (hld : σ.heap hp.ld = some (.list .arrayList dxs dm))
    (hs1 : s1 = jline (Model.txt "DISCLOSURE GROUP RECORD MISSING"))
    (hs2 : s2 = jline (Model.txt "TRY WITH DEFAULT GROUP CODE")) :
    J184 g g.args σ0 fr' ((((σ.alloc (.str s1)).2.setObj hp.ld
      (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1))).alloc (.str s2)).2.setObj hp.ld
      (.list .arrayList (dxs ++ [.ref σ.next, .ref (σ.next + 1)]) (dm + 1 + 1))) := by
  subst hs1 hs2
  have hL := Hide.elim hheap
  have hld1 : (σ.alloc (.str (jline (Model.txt "DISCLOSURE GROUP RECORD MISSING")))).2.heap hp.ld =
      some (.list .arrayList dxs dm) := heap_of_grows (grows_alloc _ _) hld
  have hL1 := loopHeap_disp_add (line := Model.txt "DISCLOSURE GROUP RECORD MISSING") hL hld
    (grows_alloc σ _) rfl ⟨σ.next, rfl, by rw [State.heap_alloc, if_pos rfl]⟩
  have hld2 : ((σ.alloc (.str (jline (Model.txt "DISCLOSURE GROUP RECORD MISSING")))).2.setObj hp.ld
      (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1))).heap hp.ld =
      some (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1)) := heap_setObj_self' hld1
  have hn2 : ((σ.alloc (.str (jline (Model.txt "DISCLOSURE GROUP RECORD MISSING")))).2.setObj hp.ld
      (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1))).next = σ.next + 1 := by
    rw [State.next_setObj, State.next_alloc]
  have hL2 := loopHeap_disp_add (line := Model.txt "TRY WITH DEFAULT GROUP CODE") hL1 hld2
    (grows_alloc _ _) rfl ⟨_, rfl, by rw [State.heap_alloc, if_pos rfl]⟩
  rw [hn2, List.append_assoc, List.singleton_append] at hL2
  have hag : Agree σ ((((σ.alloc (.str (jline (Model.txt "DISCLOSURE GROUP RECORD MISSING")))).2.setObj
      hp.ld (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1))).alloc
      (.str (jline (Model.txt "TRY WITH DEFAULT GROUP CODE")))).2.setObj hp.ld
      (.list .arrayList (dxs ++ [.ref σ.next, .ref (σ.next + 1)]) (dm + 1 + 1))) [hp.ld] :=
    agree_setObj_mem (agree_alloc (agree_setObj_mem (agree_alloc (agree_refl σ [hp.ld]) _)
      (List.mem_singleton_self _) _) _) (List.mem_singleton_self _) _
  have hns : NoStr σ [hp.ld] := by
    intro a ha s hs
    rw [List.mem_singleton] at ha
    rw [ha, hld] at hs
    cases hs
  have hsel : sel g i.toInt.toNat =
      { stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat) with
        disp := (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).disp ++
          [Model.txt "DISCLOSURE GROUP RECORD MISSING"] ++ [Model.txt "TRY WITH DEFAULT GROUP CODE"] } := by
    unfold sel selD
    rw [if_pos hm]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨i, hp, tcbV, acctV, xrefV, lastV, ts, ⟨hn, hi0, hlocs, f22, f6, f4, f5, ?_, hstop⟩, f3,
    ?_, ?_, f25, f16, f17, f28, ?_, f11, ?_, hm⟩
  · have hr := Hide.elim htcb
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    refine Hide.intro (jrecAt_agree hr hag hns (fun hm => ?_))
    rw [List.mem_singleton] at hm
    rw [hm, hld] at hxh
    cases hxh
  · rw [hsel]; exact f12
  · rw [hsel]; exact f14
  · rw [hag.2 ts (State.lt_next_of_heap hts) (fun hm => by
      rw [List.mem_singleton] at hm; rw [hm, hld] at hts; cases hts), hts]
  · rw [hsel]; exact Hide.intro hL2

set_option maxRecDepth 100000 in
theorem cp037Str_defaultGrp : cp037Str Model.defaultGrp =
    [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16, 32#16] := by decide

theorem defDisc_eq {g : G} {t : List FV} {jd : Nat}
    (hjd : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType t && Model.dCat d == Model.tCat t) = some jd) :
    ∃ h : jd < g.discs.length, defDisc g t = g.discs[jd] := by
  obtain ⟨hjl, hp, hprev⟩ := List.findIdx?_eq_some_iff_getElem.1 hjd
  refine ⟨hjl, ?_⟩
  simp only [defDisc]
  rw [Model.find?_eq_getElem _ _ jd hjl hp (fun k hk => by simpa using hprev k hk), Option.getD_some]

theorem defDisc_nil {g : G} {t : List FV}
    (hjd : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType t && Model.dCat d == Model.tCat t) = none) :
    defDisc g t = [] := by
  rw [List.findIdx?_eq_none_iff] at hjd
  have h : g.discs.find? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType t && Model.dCat d == Model.tCat t) = none := by
    rw [List.find?_eq_none]
    intro x hx
    simp [hjd x hx]
  simp only [defDisc, h, Option.getD_none]

/-- **The `DEFAULT` group's record copied** (statements 184–188): the cut point 196. -/
theorem j196_of_default {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {xs : List Value} {jd : Nat} {dk dc : Addr}
    {fsc : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hstop : (g.stE i.toInt.toNat).stop = false) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (sel g i.toInt.toNat).total)))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (sel g i.toInt.toNat).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f7 : fr'.get 7 = some (.ref dc))
    (htcb : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y) (g.trec i.toInt.toNat))
    (hheap : LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV)
    (hm : grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat) = true)
    (hds : Forall2 (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ) xs g.discs)
    (hjd : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
      Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) = some jd)
    (hdk : xs[jd]? = some (.ref dk))
    (hdc : σ1.heap dc = some (.plain "Cbact04c$DisGroupRecord" fsc))
    (hkc : ∀ key ∈ keysDC, Fields.get fsc ("Cbact04c$DisGroupRecord", key) =
      Fields.get (fieldsOf σ dk) ("Cbact04c$DisGroupRecord", key))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J196 g g.args σ0 fr' σ1 := by
  obtain ⟨hjl, hdef⟩ := defDisc_eq hjd
  have hxl := Forall2.length_eq hds
  have hjx : jd < xs.length := by omega
  have hrel := forall2_getElem hds jd hjx
  rw [List.getElem?_eq_getElem hjx] at hdk
  have hdk' : xs[jd] = .ref dk := Option.some.inj hdk
  rw [hdk'] at hrel
  obtain ⟨x0, fsk, hx0, hdkh, -⟩ := id hrel
  cases hx0
  have hdd : discD g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat) = defDisc g (g.trec i.toInt.toNat) := by
    unfold discD
    rw [if_pos hm]
  have hrc : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ1 (.ref dc)
      (discD g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat)) := by
    rw [hdd, hdef]
    rw [fieldsOf_eq hdkh] at hkc
    exact jrecAt_copy hrel hdkh hdc (same_keys disGroupRecord_jnames hkc) (strKeep_of_grows hg)
  exact ⟨i, hp, .ref y, acctV, xrefV, lastV, .ref dc, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg htcb), hstop⟩, f3, f12, f14, f25, f16, f17, f7,
    Hide.intro (loopHeap_grows hheap hg hi), Hide.intro hrc⟩

/-- **The `DEFAULT` group missing too**: the outputs after the retry lines, the abend lines. -/
theorem out_default_missing {g : G} (hin : InFacts g) {n : Nat} (hn : n < g.tcat.length)
    (hs : (g.stE n).stop = false)
    (hacc : (stSel g.xrefs (g.st n) (g.trec n)).acct ≠ [])
    (hxr : (stSel g.xrefs (g.st n) (g.trec n)).xref ≠ [])
    (hm : grpMissing g (stSel g.xrefs (g.st n) (g.trec n)) (g.trec n) = true)
    (hd : defDisc g (g.trec n) = []) :
    g.out =
      { disp := (sel g n).disp ++ [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP",
          Model.txt "FILE STATUS IS: NNNN0023", Model.txt "ABENDING PROGRAM"],
        writes := (sel g n).writes, rewrites := (sel g n).rewrites, abended := true } := by
  have e := G.stE_succ g hn
  rw [← trec_eq hn] at e
  obtain ⟨h1, h2⟩ := stepE_default_missing g (g.stE n) (g.trec n) hs hacc hxr hm hd hin.discs_ne
  rw [← e] at h1 h2
  rw [G.out_stopped g h2 (by omega)]
  have hst : g.st (n + 1) = _ := h1
  rw [hst]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

end EquivLean.Modernize.Cbact04c.Java
