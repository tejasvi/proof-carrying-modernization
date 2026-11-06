import EquivLean.Modernize.Cbact04c.JavaRunRes97

/-!
# CBACT04C → Java, `run`: statements 108–116 (the posted account stored and rewritten)

`findAcct` finds the posted account's position `j` in the table copy (the first account with its
id, `acctIdx_table`); the table gets a copy of the posted account at `j` (the model's
`replaceFirst`), the rewrite list another copy. `j125_of_rewrite`: the cut point 125.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The table copy as `findAcct` reads it -/

theorem ofInt64_inj {x y : Int} (hx1 : -9223372036854775808 ≤ x) (hx2 : x < 9223372036854775808)
    (hy1 : -9223372036854775808 ≤ y) (hy2 : y < 9223372036854775808)
    (h : BitVec.ofInt 64 x = BitVec.ofInt 64 y) : x = y := by
  have := congrArg BitVec.toInt h
  rwa [toInt_ofInt64 hx1 hx2, toInt_ofInt64 hy1 hy2] at this

theorem aId_range {a : List FV} (hv : AccountRecord.Valid a) :
    0 ≤ Model.aId a ∧ Model.aId a < 100000000000 := by
  have r := holds_display rfl (valid_num hv (i := 0) (by decide) (fmt := {digits := 11})
    (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (a.getD 0 default))
  have q := r.2 trivial
  simp only [Model.aId]
  omega

/-- The id field of a valid account record object. -/
theorem acctIdOf_rec {σ : State} {x : Value} {a : List FV}
    (h : JRecAt AccountRecord "Cbact04c$AccountRecord" σ x a) (hv : AccountRecord.Valid a) :
    acctIdOf σ x = some (BitVec.ofInt 64 (Model.aId a)) := by
  obtain ⟨y, fs, rfl, hy, hf⟩ := jrec_obj h
  exact acctIdOf_ref hy (jfield_num hf hv (i := 0) (by decide) (fmt := {digits := 11}) (by decide))

theorem forall2_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | [], [], .nil, _, hx => by simp at hx
  | _ :: _, y :: _, .cons h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hm
    · exact ⟨y, List.mem_cons_self .., h⟩
    · obtain ⟨y', hy', hr⟩ := forall2_mem_left hs x hm
      exact ⟨y', List.mem_cons_of_mem _ hy', hr⟩

theorem forall2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | [], [], .nil, _, hy => by simp at hy
  | x :: _, _ :: _, .cons h hs, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hm
    · exact ⟨x, List.mem_cons_self .., h⟩
    · obtain ⟨x', hx', hr⟩ := forall2_mem_right hs y hm
      exact ⟨x', List.mem_cons_of_mem _ hx', hr⟩

theorem acctArr_of {σ : State} {xs : List Value} {accts : List (List FV)}
    (h : Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) xs accts)
    (hv : ∀ a ∈ accts, AccountRecord.Valid a) : AcctArr σ xs := by
  intro x hx
  obtain ⟨a, ha, hr⟩ := forall2_mem_left h x hx
  obtain ⟨y, fs, rfl, hy, hf⟩ := jrec_obj hr
  exact ⟨y, fs, _, rfl, hy, jfield_num hf (hv a ha) (i := 0) (by decide) (fmt := {digits := 11})
    (by decide)⟩

theorem acct_key_mem {σ : State} {xs : List Value} {accts : List (List FV)}
    (h : Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) xs accts)
    (hv : ∀ a ∈ accts, AccountRecord.Valid a) {id : Int} (hex : ∃ a ∈ accts, Model.aId a = id) :
    ∃ x ∈ xs, acctIdOf σ x = some (BitVec.ofInt 64 id) := by
  obtain ⟨a, ha, rfl⟩ := hex
  obtain ⟨x, hx, hr⟩ := forall2_mem_right h a ha
  exact ⟨x, hx, acctIdOf_rec hr (hv a ha)⟩

/-- `findAcct`'s search over the table copy is the search over the model's table. -/
theorem findIdx_table {σ : State} {id : Int} (hid0 : 0 ≤ id) (hid1 : id < 100000000000) :
    ∀ {xs : List Value} {accts : List (List FV)},
      Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) xs accts →
      (∀ a ∈ accts, AccountRecord.Valid a) →
      xs.findIdx? (fun x => decide (acctIdOf σ x = some (BitVec.ofInt 64 id))) =
        accts.findIdx? (fun a => Model.aId a == id)
  | [], [], .nil, _ => rfl
  | _ :: _, a :: _, .cons hxa hrest, hv => by
    rw [List.findIdx?_cons, List.findIdx?_cons,
      findIdx_table hid0 hid1 hrest (fun a ha => hv a (List.mem_cons_of_mem _ ha))]
    have hva := hv a (List.mem_cons_self ..)
    rw [acctIdOf_rec hxa hva]
    have hr := aId_range hva
    by_cases he : Model.aId a = id
    · simp [he]
    · have hne : BitVec.ofInt 64 (Model.aId a) ≠ BitVec.ofInt 64 id :=
        fun h => he (ofInt64_inj (by omega) (by omega) (by omega) (by omega) h)
      simp [he, hne]

/-- **The position `findAcct` returns** for an id of the table. -/
theorem acctIdx_table {σ : State} {A : Addr} {axs : List Value} {accts : List (List FV)}
    (hA : σ.heap A = some (.array (.cls "Cbact04c$AccountRecord") axs))
    (h : Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) axs accts)
    (hv : ∀ a ∈ accts, AccountRecord.Valid a) {id : Int} (hid0 : 0 ≤ id)
    (hid1 : id < 100000000000) {j : Nat} (hj : accts.findIdx? (fun a => Model.aId a == id) = some j) :
    acctIdx σ A (BitVec.ofInt 64 id) = BitVec.ofNat 32 j := by
  simp only [acctIdx, hA, findIdx_table hid0 hid1 h hv, hj]

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The heap invariant through the stores of statements 112 and 115 -/

theorem coreHeap_mono {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {M M' : List Addr}
    (hc : CoreHeap g σ0 σ h s M) (hM : ∀ a ∈ M', a ∈ M) : CoreHeap g σ0 σ h s M' := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, ⟨rxs, rm, hlr, hrr, hrM⟩, ⟨axs, hA, haa, haM⟩, htr, hp, hcl⟩ := hc
  exact ⟨hg0, hin, hfr, hres, hdisp, hw, ⟨rxs, rm, hlr, hrr, fun v hv a hva hm => hrM v hv a hva (hM a hm)⟩,
    ⟨axs, hA, haa, fun v hv a hva hm => haM v hv a hva (hM a hm)⟩, htr, hp, hcl⟩

theorem jrec_not_at {s : Schema} {cls : ClassName} {σ : State} {x : Addr} {vals : List FV} {A : Addr}
    {o : Obj} (h : JRecAt s cls σ (.ref x) vals) (hA : σ.heap A = some o)
    (ho : ∀ fs, o ≠ .plain cls fs) : x ∉ [A] := by
  intro hm
  rw [List.mem_singleton] at hm
  subst hm
  obtain ⟨y, fs, hy, hyh, -⟩ := h
  cases hy
  rw [hA] at hyh
  cases hyh
  exact ho fs rfl

/-- **The table copy gets the posted account at `j`** (statement 112). -/
theorem coreHeap_setTable {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {axs : List Value}
    {j : Nat} {y1 : Addr} {p : List FV} (hc : CoreHeap g σ0 σ h s [])
    (hA : σ.heap h.A = some (.array (.cls "Cbact04c$AccountRecord") axs))
    (hy1 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref y1) p) :
    CoreHeap g σ0 (σ.setObj h.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1)))) h
      { s with accts := s.accts.set j p } [] := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, hr, ⟨axs', hA', haa, -⟩, htr, hp, hcl⟩ := hc
  rw [hA] at hA'
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at hA'
  subst hA'
  have ha : Agree σ (σ.setObj h.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1))))
      [h.A] := agree_setObj_mem (agree_refl σ [h.A]) (List.mem_singleton_self _) _
  have hn : NoStr σ [h.A] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hA] at hst
    cases hst
  have hnotA : ∀ x : Addr, ∀ o : Obj, σ.heap x = some o → (∀ c ys, o ≠ .array c ys) → x ∉ [h.A] := by
    intro x o hx ho hm
    rw [List.mem_singleton] at hm
    subst hm
    rw [hA] at hx
    cases hx
    exact ho _ _ rfl
  obtain ⟨fsR, hR, -⟩ := id hres
  obtain ⟨dxs, dm, hld, -⟩ := id hdisp
  obtain ⟨wxs, wm, hlw, -⟩ := id hw
  obtain ⟨rxs, rm, hlr, -⟩ := id hr
  obtain ⟨fsT, hT, -⟩ := id htr
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, -⟩ := id hfr
  refine ⟨grows_setObj hg0 h0A, inits_of_eq rfl hin, hfr,
    resAt_agree hres ha (hnotA _ _ hR (by intro c ys e; cases e)),
    dispAt_agree hdisp ha hn (hnotA _ _ hld (by intro c ys e; cases e)),
    recsAt_agree hw ha hn (hnotA _ _ hlw (by intro c ys e; cases e)) (fun a hm => ?_),
    recsAt_agree hr ha hn (hnotA _ _ hlr (by intro c ys e; cases e)) (fun a hm => ?_),
    ⟨axs.set j (.ref y1), heap_setObj_self' hA, ?_, fun _ _ _ _ hm => absurd hm List.not_mem_nil⟩,
    tranOk_agree htr ha hn (hnotA _ _ hT (by intro c ys e; cases e)),
    jstrAt_agree hp ha hn, jstrAt_agree hcl ha hn⟩
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs' he => by rw [hA] at he; cases he)
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs' he => by rw [hA] at he; cases he)
  · refine forall2_set (jrecAt_agree hy1 ha hn (jrec_not_at hy1 hA (fun fs e => by cases e))) j
      (forall2_jrecAt_agree ha hn haa (fun v hv a hva => ?_))
    obtain ⟨vals, hvr⟩ := forall2_mem_rel haa v hv
    rw [hva] at hvr
    exact jrec_not_at hvr hA (fun fs e => by cases e)

/-- **The rewrite list gets the posted account** (statement 115). -/
theorem coreHeap_rewrites_add {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {rxs : List Value}
    {rm : Nat} {v : Value} {p : List FV} (hc : CoreHeap g σ0 σ h s [])
    (hlr : σ.heap h.lr = some (.list .arrayList rxs rm))
    (hv : JRecAt AccountRecord "Cbact04c$AccountRecord" σ v p) :
    CoreHeap g σ0 (σ.setObj h.lr (.list .arrayList (rxs ++ [v]) (rm + 1))) h
      { s with rewrites := s.rewrites ++ [p] } [] := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, ⟨rxs', rm', hlr', hrr, -⟩, ht, htr, hp, hcl⟩ := hc
  rw [hlr] at hlr'
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hlr'
  obtain ⟨rfl, rfl⟩ := hlr'
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, hdw, hdl, hwl⟩ := id hfr
  refine ⟨grows_setObj hg0 h0l, inits_of_eq rfl hin, hfr, resAt_setObj_list hlr hres,
    ?_, recsAt_setObj_list hlr hwl hw,
    ⟨rxs ++ [v], rm + 1, heap_setObj_self' hlr, ?_, fun _ _ _ _ hm => absurd hm List.not_mem_nil⟩,
    tableAt_setObj_list hlr ht, tranOk_setObj_list hlr htr, jstrAt_setObj_list hlr hp,
    jstrAt_setObj_list hlr hcl⟩
  · obtain ⟨dxs, dm, hld, hdd⟩ := hdisp
    exact ⟨dxs, dm, by rw [heap_setObj_other hdl, hld],
      forall2_mono (fun _ _ hh => jstrAt_setObj_list hlr hh) hdd⟩
  · exact forall2_append (jrecAt_setObj_list hlr hv)
      (forall2_mono (fun _ _ hh => jrecAt_setObj_list hlr hh) hrr)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- The model's rewrite of the previous account: the table with the posted account at the first
position of its id, the posted account appended to the rewrites. -/
theorem stRw_some {s : Model.St} {t : List FV} {id : Int} {j : Nat} (hl : s.lastId = some id)
    (hacid : Model.aId s.acct = id)
    (hj : s.accts.findIdx? (fun a => Model.aId a == id) = some j) :
    stRw s t = { disp1 s t with accts := s.accts.set j (Model.posted s.acct s.total),
                                rewrites := s.rewrites ++ [Model.posted s.acct s.total] } := by
  rw [List.findIdx?_eq_some_iff_getElem] at hj
  obtain ⟨hjl, hp, hprev⟩ := hj
  have hrf : Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct) (Model.posted s.acct s.total)
      s.accts = s.accts.set j (Model.posted s.acct s.total) := by
    rw [hacid]
    exact Model.replaceFirst_eq_set _ _ s.accts j hjl hp (fun k hk => by simpa using hprev k hk)
  simp only [stRw, disp1, hl, Option.isSome_some, ↓reduceIte, hrf]

/-- **The posted account stored into the table copy and appended to the rewrites**
(statements 108–116): the cut point 125. -/
theorem j125_of_rewrite {g : G} {σ0 σ σ1 σ3 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {ac : Addr} {fsp : List (FieldKey × Value)} {axs rxs : List Value} {rm j : Nat} {id : Int}
    {y1 y2 : Addr} {fs1 fs2 : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hcore : Hide (CoreHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [ac]))
    (hpst : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total)))
    (hl : (g.st i.toInt.toNat).lastId = some id)
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hacid : Model.aId (g.st i.toInt.toNat).acct = id)
    (hj : (g.st i.toInt.toNat).accts.findIdx? (fun a => Model.aId a == id) = some j)
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fsp))
    (hA : σ.heap hp.A = some (.array (.cls "Cbact04c$AccountRecord") axs))
    (hlr : σ.heap hp.lr = some (.list .arrayList rxs rm)) (hacA : ac ≠ hp.A) (hlrA : hp.lr ≠ hp.A)
    (hy1 : σ1.heap y1 = some (.plain "Cbact04c$AccountRecord" fs1))
    (hk1 : ∀ k ∈ keysAC, Fields.get fs1 ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf σ ac) ("Cbact04c$AccountRecord", k))
    (hg1 : Grows σ σ1) (hi1 : σ1.inits = σ.inits)
    (hy2 : σ3.heap y2 = some (.plain "Cbact04c$AccountRecord" fs2))
    (hk2 : ∀ k ∈ keysAC, Fields.get fs2 ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord")
        (axs.set j (.ref y1)))) ac) ("Cbact04c$AccountRecord", k))
    (hg3 : Grows (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1)))) σ3)
    (hi3 : σ3.inits = (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord")
      (axs.set j (.ref y1)))).inits) :
    J125 g g.args σ0 fr' (σ3.setObj hp.lr (.list .arrayList (rxs ++ [.ref y2]) (rm + 1))) := by
  have hpst' := Hide.elim hpst
  -- the first copy holds the posted account
  have hr1 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ1 (.ref y1)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total) := by
    rw [fieldsOf_eq hac] at hk1
    exact jrecAt_copy hpst' hac hy1 (same_keys accountRecord_jnames hk1) (strKeep_of_grows hg1)
  -- the table copy gets it at `j`
  have hA1 : σ1.heap hp.A = some (.array (.cls "Cbact04c$AccountRecord") axs) := heap_of_grows hg1 hA
  have hc1 := coreHeap_grows (coreHeap_mono (Hide.elim hcore) (fun a h => absurd h List.not_mem_nil))
    hg1 hi1
  have hc2 := coreHeap_setTable (j := j) hc1 hA1 hr1
  -- the second copy (the account object is not the table)
  have hac2 : (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1)))).heap ac =
      some (.plain "Cbact04c$AccountRecord" fsp) := by
    rw [heap_setObj_other hacA]; exact heap_of_grows hg1 hac
  have hpst2 : JRecAt AccountRecord "Cbact04c$AccountRecord"
      (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1)))) (.ref ac)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total) := by
    have h1 := jrecAt_grows hg1 hpst'
    have hn' : NoStr σ1 [hp.A] := by
      intro w hw' st hst
      rw [List.mem_singleton] at hw'
      subst hw'
      rw [hA1] at hst
      cases hst
    exact jrecAt_agree h1 (agree_setObj_mem (agree_refl σ1 [hp.A]) (List.mem_singleton_self _) _) hn'
      (fun hm => hacA (List.mem_singleton.1 hm))
  have hr2 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ3 (.ref y2)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total) := by
    rw [fieldsOf_eq hac2] at hk2
    exact jrecAt_copy hpst2 hac2 hy2 (same_keys accountRecord_jnames hk2) (strKeep_of_grows hg3)
  have hc3 := coreHeap_grows hc2 hg3 hi3
  have hlr3 : σ3.heap hp.lr = some (.list .arrayList rxs rm) := by
    apply heap_of_grows hg3
    rw [heap_setObj_other hlrA]
    exact heap_of_grows hg1 hlr
  have hc4 := coreHeap_rewrites_add hc3 hlr3 hr2
  -- the record object read is not changed
  have hy0 : y ∉ [hp.A] := by
    obtain ⟨x, fsy, hx, hyh, -⟩ := Hide.elim htcb
    cases hx
    intro hm
    rw [List.mem_singleton] at hm
    subst hm
    rw [hA] at hyh
    cases hyh
  refine ⟨i, hp, .ref y, ⟨hn, hi0, hlocs, f22, f6, f4, f5, ?_⟩, hne, f3, f14, ?_⟩
  · have h1 := jrecAt_grows hg1 (Hide.elim htcb)
    have hn1 : NoStr σ1 [hp.A] := by
      intro w hw' st hst
      rw [List.mem_singleton] at hw'
      subst hw'
      rw [hA1] at hst
      cases hst
    have h2 := jrecAt_agree h1 (agree_setObj_mem (agree_refl σ1 [hp.A]) (List.mem_singleton_self _)
      (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1)))) hn1 hy0
    exact Hide.intro (jrecAt_setObj_list hlr3 (jrecAt_grows hg3 h2))
  · rw [stRw_some hl hacid hj]
    exact Hide.intro hc4

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

theorem stRw1_eq {s : Model.St} {t : List FV} {id : Int} {j : Nat} (hacid : Model.aId s.acct = id)
    (hj : s.accts.findIdx? (fun a => Model.aId a == id) = some j) :
    stRw1 s t = { disp1 s t with accts := (disp1 s t).accts.set j (Model.posted s.acct s.total) } := by
  rw [List.findIdx?_eq_some_iff_getElem] at hj
  obtain ⟨hjl, hp, hprev⟩ := hj
  have hrf : Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct) (Model.posted s.acct s.total)
      s.accts = s.accts.set j (Model.posted s.acct s.total) := by
    rw [hacid]
    exact Model.replaceFirst_eq_set _ _ s.accts j hjl hp (fun k hk => by simpa using hprev k hk)
  simp only [stRw1, hrf, disp1]

theorem stRw_eq_rw1 {s : Model.St} {t : List FV} {id : Int} (hl : s.lastId = some id) :
    stRw s t = { stRw1 s t with rewrites := (stRw1 s t).rewrites ++ [Model.posted s.acct s.total] } := by
  simp only [stRw, stRw1, disp1, hl, Option.isSome_some, ↓reduceIte]

/-- **The posted account stored into the table copy** (statements 108–112): the cut point 113. -/
theorem j113_of_store {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {ac : Addr} {fsp : List (FieldKey × Value)} {axs : List Value} {j : Nat} {id : Int}
    {y1 : Addr} {fs1 : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f16 : fr'.get 16 = some (.ref ac))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hcore : Hide (CoreHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [ac]))
    (hpst : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total)))
    (hsome : (g.st i.toInt.toNat).lastId.isSome)
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hacid : Model.aId (g.st i.toInt.toNat).acct = id)
    (hj : (g.st i.toInt.toNat).accts.findIdx? (fun a => Model.aId a == id) = some j)
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fsp))
    (hA : σ.heap hp.A = some (.array (.cls "Cbact04c$AccountRecord") axs)) (hacA : ac ≠ hp.A)
    (hy1 : σ1.heap y1 = some (.plain "Cbact04c$AccountRecord" fs1))
    (hk1 : ∀ k ∈ keysAC, Fields.get fs1 ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf σ ac) ("Cbact04c$AccountRecord", k))
    (hg1 : Grows σ σ1) (hi1 : σ1.inits = σ.inits) :
    J113 g g.args σ0 fr' (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord")
      (axs.set j (.ref y1)))) := by
  have hpst' := Hide.elim hpst
  have hr1 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ1 (.ref y1)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total) := by
    rw [fieldsOf_eq hac] at hk1
    exact jrecAt_copy hpst' hac hy1 (same_keys accountRecord_jnames hk1) (strKeep_of_grows hg1)
  have hA1 : σ1.heap hp.A = some (.array (.cls "Cbact04c$AccountRecord") axs) := heap_of_grows hg1 hA
  have hc1 := coreHeap_grows (coreHeap_mono (Hide.elim hcore) (fun a h => absurd h List.not_mem_nil))
    hg1 hi1
  have hc2 := coreHeap_setTable (j := j) hc1 hA1 hr1
  have hn1 : NoStr σ1 [hp.A] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hA1] at hst
    cases hst
  have hag : Agree σ1 (σ1.setObj hp.A (.array (.cls "Cbact04c$AccountRecord") (axs.set j (.ref y1))))
      [hp.A] := agree_setObj_mem (agree_refl σ1 [hp.A]) (List.mem_singleton_self _) _
  have hy0 : y ∉ [hp.A] := by
    obtain ⟨x, fsy, hx, hyh, -⟩ := Hide.elim htcb
    cases hx
    intro hm
    rw [List.mem_singleton] at hm
    subst hm
    rw [hA] at hyh
    cases hyh
  refine ⟨i, hp, .ref y, ac, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_agree (jrecAt_grows hg1 (Hide.elim htcb)) hag hn1 hy0)⟩, hsome, hne, f3, f14,
    f16, ?_, Hide.intro (jrecAt_agree (jrecAt_grows hg1 hpst') hag hn1
      (fun hm => hacA (List.mem_singleton.1 hm)))⟩
  rw [stRw1_eq hacid hj]
  exact Hide.intro hc2

/-- **The posted account appended to the rewrites** (statements 113–116): the cut point 125. -/
theorem j125_of_rw {g : G} {σ0 σ σ3 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {ac : Addr} {fsp : List (FieldKey × Value)} {rxs : List Value} {rm : Nat} {id : Int}
    {y2 : Addr} {fs2 : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hcore : Hide (CoreHeap g σ0 σ hp (stRw1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) []))
    (hpst : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total)))
    (hl : (g.st i.toInt.toNat).lastId = some id)
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fsp))
    (hlr : σ.heap hp.lr = some (.list .arrayList rxs rm))
    (hy2 : σ3.heap y2 = some (.plain "Cbact04c$AccountRecord" fs2))
    (hk2 : ∀ k ∈ keysAC, Fields.get fs2 ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf σ ac) ("Cbact04c$AccountRecord", k))
    (hg3 : Grows σ σ3) (hi3 : σ3.inits = σ.inits) :
    J125 g g.args σ0 fr' (σ3.setObj hp.lr (.list .arrayList (rxs ++ [.ref y2]) (rm + 1))) := by
  have hr2 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ3 (.ref y2)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total) := by
    rw [fieldsOf_eq hac] at hk2
    exact jrecAt_copy (Hide.elim hpst) hac hy2 (same_keys accountRecord_jnames hk2)
      (strKeep_of_grows hg3)
  have hc3 := coreHeap_grows (Hide.elim hcore) hg3 hi3
  have hlr3 : σ3.heap hp.lr = some (.list .arrayList rxs rm) := heap_of_grows hg3 hlr
  have hc4 := coreHeap_rewrites_add hc3 hlr3 hr2
  refine ⟨i, hp, .ref y, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_setObj_list hlr3 (jrecAt_grows hg3 (Hide.elim htcb)))⟩, hne, f3, f14, ?_⟩
  rw [stRw_eq_rw1 hl]
  exact Hide.intro hc4

end EquivLean.Modernize.Cbact04c.Java
