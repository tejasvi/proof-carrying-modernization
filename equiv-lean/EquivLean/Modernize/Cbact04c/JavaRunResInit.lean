import EquivLean.Modernize.Cbact04c.JavaRunRes242

/-!
# CBACT04C → Java, `run`: closing the cut points of the entry path (28, 38, 47, 57, 63, 70)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem noStr_nil (σ : State) : NoStr σ [] := fun _ hw => absurd hw List.not_mem_nil

/-- `InitAt` after a stretch that changed no object of `σ`. -/
theorem initAt_of {g : G} {σ0 σ σ' : State} {fr' : Frame} {res ld lw lr A : Addr}
    (ht : Hide (TableAt σ A g.accts [])) (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hw : Hide (RecsAt TranRecord "Cbact04c$TranRecord" σ lw [] []))
    (hr : Hide (RecsAt AccountRecord "Cbact04c$AccountRecord" σ lr [] []))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr) (hg : Grows σ0 σ)
    (hin : Inits σ) (ha : Agree σ σ' []) (hi : σ'.inits = σ.inits)
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f24 : fr'.get 24 = some (.ref g.cs))
    (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f41 : fr'.get 41 = some (.ref A)) :
    InitAt g σ0 fr' σ' res ld lw lr A := by
  have hn := noStr_nil σ
  have hMW : ∀ (cls : ClassName), ∀ a ∈ ([] : List Addr), a ∈ ([] : List Addr) ∨
      ∀ fs, σ.heap a ≠ some (.plain cls fs) := fun _ _ h => absurd h List.not_mem_nil
  exact ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41,
    Hide.intro (tableAt_agree (Hide.elim ht) ha hn List.not_mem_nil (hMW _)),
    Hide.intro (resAt_agree (Hide.elim hres) ha List.not_mem_nil),
    Hide.intro (dispAt_agree (Hide.elim hdisp) ha hn List.not_mem_nil),
    Hide.intro (recsAt_agree (Hide.elim hw) ha hn List.not_mem_nil (hMW _)),
    Hide.intro (recsAt_agree (Hide.elim hr) ha hn List.not_mem_nil (hMW _)),
    hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3,
    grows_trans hg ⟨ha.1, fun x hx => ha.2 x hx List.not_mem_nil⟩, inits_of_eq hi hin⟩

/-- The copy loop's head after one more account (statements 29–33). -/
theorem j28_of_copy {g : G} {σ0 σ σc : State} {fr' : Frame} {j : I32} {res ld lw lr A y w : Addr}
    {cxs : List Value} {fs fs' : List (FieldKey × Value)}
    (hj0 : 0 ≤ j.toInt) (hc : j.toInt < g.accts.length) (hlenA : g.accts.length < 2147483648)
    (hcxlen : cxs.length = j.toInt.toNat)
    (hA : σ.heap A = some (.array (.cls "Cbact04c$AccountRecord")
      (cxs ++ List.replicate (g.accts.length - j.toInt.toNat) .null)))
    (hcopies : Hide (Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) cxs
      (g.accts.take j.toInt.toNat)))
    (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hlw : σ.heap lw = some (.list .arrayList [] 0)) (hlr : σ.heap lr = some (.list .arrayList [] 0))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr)
    (hgn : σ0.next ≤ σ.next) (hgf : ∀ x, x < σ0.next → σ.heap x = σ0.heap x) (hin : Inits σ)
    (hrec : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ0 (.ref y)
      (g.accts[j.toInt.toNat]'(by omega))))
    (hy : σ.heap y = some (.plain "Cbact04c$AccountRecord" fs))
    (hwn : σ.next ≤ w) (hwh : σc.heap w = some (.plain "Cbact04c$AccountRecord" fs'))
    (hk : ∀ k ∈ keysAC, Fields.get fs' ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf σ y) ("Cbact04c$AccountRecord", k))
    (hcn : σ.next ≤ σc.next) (hcf : ∀ x, x < σ.next → σc.heap x = σ.heap x)
    (hci : σc.inits = σ.inits)
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f24 : fr'.get 24 = some (.ref g.cs))
    (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f22 : fr'.get 22 = some (.int (BitVec.ofNat 32 g.accts.length)))
    (f41 : fr'.get 41 = some (.ref A)) (f18 : fr'.get 18 = some (.int (j + 1#32))) :
    J28 g g.args σ0 fr' (σc.setObj A (.array (.cls "Cbact04c$AccountRecord")
      (cxs ++ (List.replicate (g.accts.length - j.toInt.toNat) .null).set 0 (.ref w)))) := by
  have hj1 := i32_toInt_add_one j hj0 (by omega)
  have hAn : A < σ.next := State.lt_next_of_heap hA
  -- the state agrees with `σ` outside the array
  have hag : Agree σ (σc.setObj A (.array (.cls "Cbact04c$AccountRecord")
      (cxs ++ (List.replicate (g.accts.length - j.toInt.toNat) .null).set 0 (.ref w)))) [A] :=
    agree_setObj_mem ⟨hcn, fun x hx _ => hcf x hx⟩ (List.mem_singleton_self A) _
  have hnA : NoStr σ [A] := by
    intro a ha s hs
    rw [List.mem_singleton] at ha
    rw [ha, hA] at hs
    cases hs
  have hplainA : ∀ (cls : ClassName) (a : Addr) (fs0 : List (FieldKey × Value)),
      σ.heap a = some (.plain cls fs0) → a ∉ [A] := by
    intro cls a fs0 h hm
    rw [List.mem_singleton] at hm
    rw [hm, hA] at h
    cases h
  have hlistA : ∀ (a : Addr) (k : ListKind) (xs : List Value) (m : Nat),
      σ.heap a = some (.list k xs m) → a ∉ [A] := by
    intro a k xs m h hm
    rw [List.mem_singleton] at hm
    rw [hm, hA] at h
    cases h
  have hwA : w ≠ A := by intro e; rw [e] at hwn; jomega
  have hres1 := Hide.elim hres
  obtain ⟨fsR, hR, -⟩ := id hres1
  obtain ⟨dxs, dm, hld, -⟩ := id (Hide.elim hdisp)
  -- the new copy holds the record
  have hrec2 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref y)
      (g.accts[j.toInt.toNat]'(by omega)) := jrecAt_grows ⟨hgn, hgf⟩ (Hide.elim hrec)
  have hnew : JRecAt AccountRecord "Cbact04c$AccountRecord"
      (σc.setObj A (.array (.cls "Cbact04c$AccountRecord")
        (cxs ++ (List.replicate (g.accts.length - j.toInt.toNat) .null).set 0 (.ref w))))
      (.ref w) (g.accts[j.toInt.toNat]'(by omega)) := by
    refine jrecAt_copy hrec2 hy (by rw [heap_setObj_other hwA, hwh])
      (same_keys accountRecord_jnames (fun k hk' => by rw [hk k hk', fieldsOf_eq hy])) ?_
    intro a s hs
    have hsa : a ≠ A := fun e => hnA a (List.mem_singleton.2 e) s hs
    rw [heap_setObj_other hsa, hcf a (State.lt_next_of_heap hs), hs]
  refine ⟨j + 1#32, res, ld, lw, lr, A, cxs ++ [.ref w], f1, f36, f40, f8, f37, f24, f10, f19, f20,
    f21, f22, f41, f18, by omega, by omega,
    by simp only [List.length_append, List.length_singleton, hcxlen, hj1]; omega, ?_, ?_, ?_, ?_, ?_, ?_,
    hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, ?_, ?_⟩
  · -- the array
    rw [heap_setObj_self' (by rw [hcf A hAn, hA])]
    have hn1 : g.accts.length - j.toInt.toNat = (g.accts.length - (j + 1#32).toInt.toNat) + 1 := by
      rw [hj1]; omega
    rw [hn1, List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
  · -- the copies
    have htake : g.accts.take (j + 1#32).toInt.toNat =
        g.accts.take j.toInt.toNat ++ [g.accts[j.toInt.toNat]'(by omega)] := by
      rw [hj1, show (j.toInt + 1).toNat = j.toInt.toNat + 1 by omega, List.take_succ,
        List.getElem?_eq_getElem (by omega), Option.toList_some]
    rw [htake]
    refine Hide.intro (forall2_append hnew (forall2_jrecAt_agree hag hnA (Hide.elim hcopies) ?_))
    intro v hv a hva
    obtain ⟨vals', hrel⟩ := forall2_mem_rel (Hide.elim hcopies) v hv
    obtain ⟨b, fsb, hb, hbh, -⟩ := jrec_obj hrel
    rw [hva] at hb
    cases hb
    exact hplainA _ _ _ hbh
  · exact Hide.intro (resAt_agree hres1 hag (hplainA _ _ _ hR))
  · exact Hide.intro (dispAt_agree (Hide.elim hdisp) hag hnA (hlistA _ _ _ _ hld))
  · rw [heap_setObj_other (fun e => hlistA _ _ _ _ hlw (List.mem_singleton.2 e)),
      hcf lw (State.lt_next_of_heap hlw), hlw]
  · rw [heap_setObj_other (fun e => hlistA _ _ _ _ hlr (List.mem_singleton.2 e)),
      hcf lr (State.lt_next_of_heap hlr), hlr]
  · exact grows_setObj (grows_post ⟨hgn, hgf⟩ hcn hcf) hA0
  · exact inits_of_eq hci hin

/-- The cut at 38: the account table is complete; the first category record object is built
(statements 34–37: a new object, two `spaces` calls, the constructor). -/
theorem ji38_of {g : G} {σ0 σ σa σb σc : State} {fr' : Frame} {j : I32} {res ld lw lr A : Addr}
    {cxs : List Value} {o : Obj}
    (hc : (g.accts.length : Int) ≤ j.toInt) (hjlen : j.toInt ≤ g.accts.length)
    (hA : σ.heap A = some (.array (.cls "Cbact04c$AccountRecord")
      (cxs ++ List.replicate (g.accts.length - j.toInt.toNat) .null)))
    (hcopies : Hide (Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) cxs
      (g.accts.take j.toInt.toNat)))
    (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hlw : σ.heap lw = some (.list .arrayList [] 0)) (hlr : σ.heap lr = some (.list .arrayList [] 0))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr)
    (hgn : σ0.next ≤ σ.next) (hgf : ∀ x, x < σ0.next → σ.heap x = σ0.heap x) (hin : Inits σ)
    (h1n : σ.next + 1 ≤ σa.next)
    (h1f : ∀ x, x < σ.next + 1 → σa.heap x = if x = σ.next then some o else σ.heap x)
    (h2n : σa.next ≤ σb.next) (h2f : ∀ x, x < σa.next → σb.heap x = σa.heap x)
    (hcf : ∀ y, ¬y = σ.next → σc.heap y = σb.heap y) (hcn : σc.next = σb.next)
    (hci : σc.inits = σ.inits)
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f24 : fr'.get 24 = some (.ref g.cs))
    (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f41 : fr'.get 41 = some (.ref A)) :
    JI g g.args σ0 fr' σc := by
  have hj : j.toInt.toNat = g.accts.length := by omega
  have hag : Agree σ σc [] := ⟨by rw [hcn]; jomega, fun x hx _ => by
    rw [hcf x (by jomega), h2f x (by jomega), h1f x (by jomega), if_neg (by jomega)]⟩
  refine ⟨res, ld, lw, lr, A, initAt_of ?_ hres hdisp ?_ ?_ hr0 hd0 hw0 hl0 hA0 hd1 hd2 hd3
    ⟨hgn, hgf⟩ hin hag hci f1 f36 f40 f8 f37 f24 f10 f19 f20 f21 f41⟩
  · refine Hide.intro ⟨cxs, ?_, ?_, fun _ _ _ _ h => absurd h List.not_mem_nil⟩
    · rw [hA, hj, Nat.sub_self, List.replicate_zero, List.append_nil]
    · have h2 := Hide.elim hcopies
      rwa [hj, List.take_of_length_le (Nat.le_refl _)] at h2
  · exact Hide.intro ⟨[], 0, hlw, .nil, fun _ h => absurd h List.not_mem_nil⟩
  · exact Hide.intro ⟨[], 0, hlr, .nil, fun _ h => absurd h List.not_mem_nil⟩

/-- `InitAt` after a stretch that changed only the transaction object `T`. -/
theorem initAt_agreeT {g : G} {σ0 σ σ' : State} {fr' : Frame} {res ld lw lr A T : Addr}
    {fsT : List (FieldKey × Value)} (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fsT))
    (hT0 : σ0.next ≤ T)
    (ht : Hide (TableAt σ A g.accts [])) (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hw : Hide (RecsAt TranRecord "Cbact04c$TranRecord" σ lw [] []))
    (hr : Hide (RecsAt AccountRecord "Cbact04c$AccountRecord" σ lr [] []))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr) (hg : Grows σ0 σ)
    (hin : Inits σ) (ha : Agree σ σ' [T]) (hi : σ'.inits = σ.inits)
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f24 : fr'.get 24 = some (.ref g.cs))
    (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f41 : fr'.get 41 = some (.ref A)) :
    InitAt g σ0 fr' σ' res ld lw lr A := by
  have hn : NoStr σ [T] := by
    intro a hm s hs
    rw [List.mem_singleton] at hm
    rw [hm, hT] at hs
    cases hs
  have hnot : ∀ (a : Addr) (o : Obj), σ.heap a = some o →
      (∀ fs, o ≠ .plain "Cbact04c$TranRecord" fs) → a ∉ [T] := by
    intro a o h hne hm
    rw [List.mem_singleton] at hm
    rw [hm, hT] at h
    cases h
    exact hne fsT rfl
  have hres1 := Hide.elim hres
  obtain ⟨fsR, hR, -⟩ := id hres1
  obtain ⟨dxs, dm, hld, -⟩ := id (Hide.elim hdisp)
  obtain ⟨wxs, wm, hlw, hwx, -⟩ := id (Hide.elim hw)
  obtain ⟨rxs, rm, hlr, hrx, -⟩ := id (Hide.elim hr)
  obtain ⟨axs, hA, -⟩ := id (Hide.elim ht)
  have hwx' : wxs = [] := by cases hwx; rfl
  have hrx' : rxs = [] := by cases hrx; rfl
  subst hwx' hrx'
  have hMW : ∀ a ∈ [T], a ∈ ([] : List Addr) ∨
      ∀ fs, σ.heap a ≠ some (.plain "Cbact04c$AccountRecord" fs) := by
    intro a hm
    rw [List.mem_singleton] at hm
    rw [hm, hT]
    exact Or.inr (fun fs h => by simp at h)
  exact ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41,
    Hide.intro (tableAt_agree (Hide.elim ht) ha hn
      (hnot _ _ hA (fun _ h => by simp at h)) hMW),
    Hide.intro (resAt_agree hres1 ha (hnot _ _ hR (fun _ h => by simp at h))),
    Hide.intro (dispAt_agree (Hide.elim hdisp) ha hn (hnot _ _ hld (fun _ h => by simp at h))),
    Hide.intro ⟨[], wm, by rw [ha.2 lw (State.lt_next_of_heap hlw)
      (hnot _ _ hlw (fun _ h => by simp at h)), hlw], .nil, fun _ h => absurd h List.not_mem_nil⟩,
    Hide.intro ⟨[], rm, by rw [ha.2 lr (State.lt_next_of_heap hlr)
      (hnot _ _ hlr (fun _ h => by simp at h)), hlr], .nil, fun _ h => absurd h List.not_mem_nil⟩,
    hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3,
    ⟨Nat.le_trans hg.1 ha.1, fun x hx => by
      rw [ha.2 x (Nat.lt_of_lt_of_le hx hg.1) (fun hm => by
        rw [List.mem_singleton] at hm; subst hm; jomega), hg.2 x hx]⟩,
    inits_of_eq hi hin⟩

/-- The cut at 70: the transaction object is built (statements 63–69: six `spaces` calls and its
constructor). -/
theorem ji70_of {g : G} {σ0 σ σ1 σ2 σ3 σ4 σ5 σ6 σc : State} {fr' : Frame}
    {res ld lw lr A T d w6 : Addr} {acctV v17 : Value} {fs fs' : List (FieldKey × Value)}
    (ht : Hide (TableAt σ A g.accts [])) (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hw : Hide (RecsAt TranRecord "Cbact04c$TranRecord" σ lw [] []))
    (hr : Hide (RecsAt AccountRecord "Cbact04c$AccountRecord" σ lr [] []))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr) (hg : Grows σ0 σ)
    (hin : Inits σ) (hT0 : σ0.next ≤ T)
    (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fs))
    (hd : σ.heap d = some (.str (spJ 100)))
    (h1n : σ.next ≤ σ1.next) (h1f : ∀ x, x < σ.next → σ1.heap x = σ.heap x)
    (h2n : σ1.next ≤ σ2.next) (h2f : ∀ x, x < σ1.next → σ2.heap x = σ1.heap x)
    (h3n : σ2.next ≤ σ3.next) (h3f : ∀ x, x < σ2.next → σ3.heap x = σ2.heap x)
    (h4n : σ3.next ≤ σ4.next) (h4f : ∀ x, x < σ3.next → σ4.heap x = σ3.heap x)
    (h5n : σ4.next ≤ σ5.next) (h5f : ∀ x, x < σ4.next → σ5.heap x = σ4.heap x)
    (h6n : σ5.next ≤ σ6.next) (h6f : ∀ x, x < σ5.next → σ6.heap x = σ5.heap x)
    (hw6 : σ6.heap w6 = some (.str (spJ 20)))
    (hcT : σc.heap T = some (.plain "Cbact04c$TranRecord" fs'))
    (hk : ∀ k ∈ keysTR, ∃ v, Fields.get fs' ("Cbact04c$TranRecord", k) = some v)
    (hdesc : Fields.get fs' ("Cbact04c$TranRecord", "tranDesc") = some (.ref d))
    (hfil : Fields.get fs' ("Cbact04c$TranRecord", "filler1") = some (.ref w6))
    (hcf : ∀ y, ¬y = T → σc.heap y = σ6.heap y) (hcn : σc.next = σ6.next)
    (hci : σc.inits = σ.inits)
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f24 : fr'.get 24 = some (.ref g.cs))
    (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f41 : fr'.get 41 = some (.ref A)) (f16 : fr'.get 16 = some acctV)
    (f38 : fr'.get 38 = some (.ref T)) (f17 : fr'.get 17 = some v17) :
    JI70 g g.args σ0 fr' σc := by
  -- the six callee states keep every older object
  have h6 : ∀ x, x < σ.next → σ6.heap x = σ.heap x := by
    intro x hx
    rw [h6f x (by jomega), h5f x (by jomega), h4f x (by jomega), h3f x (by jomega),
      h2f x (by jomega), h1f x hx]
  have hag : Agree σ σc [T] := ⟨by rw [hcn]; jomega, fun x hx hm => by
    rw [hcf x (fun e => hm (List.mem_singleton.2 e)), h6 x hx]⟩
  have hdT : d ≠ T := by intro e; rw [e, hT] at hd; cases hd
  have hd' : σc.heap d = some (.str (spJ 100)) := by
    rw [hag.2 d (State.lt_next_of_heap hd) (fun hm => hdT (List.mem_singleton.1 hm)), hd]
  have hT6 : σ6.heap T = some (.plain "Cbact04c$TranRecord" fs) := by
    rw [h6 T (State.lt_next_of_heap hT), hT]
  have hwT : w6 ≠ T := by intro e; rw [e, hT6] at hw6; cases hw6
  have hw6' : σc.heap w6 = some (.str (spJ 20)) := by rw [hcf w6 hwT, hw6]
  refine ⟨res, ld, lw, lr, A, acctV, T, initAt_agreeT hT hT0 ht hres hdisp hw hr hr0 hd0 hw0 hl0
    hA0 hd1 hd2 hd3 hg hin hag hci f1 f36 f40 f8 f37 f24 f10 f19 f20 f21 f41, f16, f38, hT0,
    Hide.intro ⟨fs', hcT, hk, ⟨d, spJ 100, hdesc, hd', spJ_length 100, ?_⟩, ⟨w6, hfil, hw6'⟩⟩,
    v17, f17⟩
  simp [spJ]

end EquivLean.Modernize.Cbact04c.Java
