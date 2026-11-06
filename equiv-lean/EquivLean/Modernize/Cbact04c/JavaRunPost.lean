import EquivLean.Modernize.Cbact04c.JavaRunRunHeap

/-!
# CBACT04C → Java, `run`: field writes to record objects; the remainder of `trunc`

* `jrecAt_set`: a field write to a record object holds the record with that field replaced;
  `jrecAt_posted`: the three writes of the posting (balance, cycle credit and debit);
* `coreHeap_setObj_acct`: writing the current account object keeps the loop's heap invariant;
* `srem_add_mod`: `trunc (x + y, …)` on machine longs is the integer `tmod`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## Field writes -/

/-- A field write keeps the other fields of a record object. -/
theorem jfieldAt_set_other {σ σ' : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {k : FieldKey} {w : Value} {f : Field} {val : FV} (h : jFieldAt σ cls fs f val)
    (hk : (cls, f.jname) ≠ k) (hs : StrKeep σ σ') : jFieldAt σ' cls (Fields.set fs k w) f val :=
  jfieldAt_copy h (by rw [fields_get_set, if_neg hk]) hs

theorem forall2_jfield_set_other {σ σ' : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    (hs : StrKeep σ σ') {k : String} {w : Value} :
    ∀ {fields : List Field} {vals : List FV},
      Forall2 (fun f val => jFieldAt σ cls fs f val) fields vals →
      k ∉ fields.map (·.jname) →
      Forall2 (fun f val => jFieldAt σ' cls (Fields.set fs (cls, k) w) f val) fields vals
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hrest, hk => by
      simp only [List.map_cons, List.mem_cons, not_or] at hk
      exact .cons (jfieldAt_set_other h (fun he => hk.1 (congrArg Prod.snd he).symm) hs)
        (forall2_jfield_set_other hs hrest hk.2)

theorem forall2_jfield_set {σ σ' : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    (hs : StrKeep σ σ') {k : String} {w : Value} {val' : FV}
    (hnew : ∀ f : Field, f.jname = k → jFieldAt σ' cls (Fields.set fs (cls, k) w) f val') :
    ∀ {fields : List Field} {vals : List FV} {i : Nat},
      Forall2 (fun f val => jFieldAt σ cls fs f val) fields vals →
      (fields.map (·.jname)).Nodup → (fields.map (·.jname))[i]? = some k →
      Forall2 (fun f val => jFieldAt σ' cls (Fields.set fs (cls, k) w) f val) fields
        (vals.set i val')
  | [], [], _, .nil, _, hi => by simp at hi
  | f :: _, _ :: _, 0, .cons _ hrest, hnd, hi => by
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
      simp only [List.map_cons, List.nodup_cons] at hnd
      refine .cons (hnew f hi) (forall2_jfield_set_other hs hrest ?_)
      rw [← hi]; exact hnd.1
  | f :: _, _ :: _, i + 1, .cons h hrest, hnd, hi => by
      simp only [List.map_cons, List.getElem?_cons_succ] at hi
      simp only [List.map_cons, List.nodup_cons] at hnd
      refine .cons (jfieldAt_set_other h ?_ hs) (forall2_jfield_set hs hnew hrest hnd.2 hi)
      intro he
      have hk : f.jname = k := congrArg Prod.snd he
      exact hnd.1 (hk ▸ List.mem_of_getElem? hi)

/-- **A field write to a record object**: the object holds the record with field `i` replaced. -/
theorem jrecAt_set {s : Schema} {cls : ClassName} {σ : State} {x : Addr}
    {fs : List (FieldKey × Value)} {vals : List FV} {i : Nat} {k : String} {w : Value} {val' : FV}
    (h : JRecAt s cls σ (.ref x) vals) (hx : σ.heap x = some (.plain cls fs))
    (hnd : (s.fields.map (·.jname)).Nodup) (hi : (s.fields.map (·.jname))[i]? = some k)
    (hnew : ∀ f : Field, f.jname = k →
      jFieldAt (σ.setObj x (.plain cls (Fields.set fs (cls, k) w))) cls (Fields.set fs (cls, k) w)
        f val') :
    JRecAt s cls (σ.setObj x (.plain cls (Fields.set fs (cls, k) w))) (.ref x) (vals.set i val') := by
  obtain ⟨y, fs0, hy, hyh, hf⟩ := h
  cases hy
  rw [hx] at hyh
  cases hyh
  refine ⟨x, _, rfl, heap_setObj_self' hx, forall2_jfield_set ?_ hnew hf hnd hi⟩
  intro a s' ha
  rw [heap_setObj_other]
  · exact ha
  · intro hax
    subst hax
    rw [hx] at ha
    cases ha

/-- A numeric field written with a long. -/
theorem jfieldAt_set_num {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {k : String}
    (v : Int) (f : Field) (hf : f.jname = k) :
    jFieldAt σ cls (Fields.set fs (cls, k) (.long (BitVec.ofInt 64 v))) f (.num v) := by
  show Fields.get _ _ = _
  rw [fields_get_set, if_pos (by rw [hf])]

/-! ## The posting of the current account -/

theorem keysAC_nodup : keysAC.Nodup := by decide

/-- **The posting** (statements 105–107): the account object holds `Model.posted`. -/
theorem jrecAt_posted {σ : State} {ac : Addr} {fsa : List (FieldKey × Value)} {acct : List FV}
    {total : Int} (h : JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac) acct)
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fsa)) :
    JRecAt AccountRecord "Cbact04c$AccountRecord"
      (((σ.setObj ac (.plain "Cbact04c$AccountRecord" (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal")
          (.long (BitVec.ofInt 64 (Int.tmod (Model.aBal acct + total) (10 ^ 12))))))).setObj ac
        (.plain "Cbact04c$AccountRecord" (Fields.set (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal")
          (.long (BitVec.ofInt 64 (Int.tmod (Model.aBal acct + total) (10 ^ 12)))))
          ("Cbact04c$AccountRecord", "acctCurrCycCredit") (.long (BitVec.ofInt 64 0))))).setObj ac
        (.plain "Cbact04c$AccountRecord" (Fields.set (Fields.set (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal")
          (.long (BitVec.ofInt 64 (Int.tmod (Model.aBal acct + total) (10 ^ 12)))))
          ("Cbact04c$AccountRecord", "acctCurrCycCredit") (.long (BitVec.ofInt 64 0)))
          ("Cbact04c$AccountRecord", "acctCurrCycDebit") (.long (BitVec.ofInt 64 0)))))
      (.ref ac) (Model.posted acct total) := by
  have hnd : (AccountRecord.fields.map (·.jname)).Nodup := by
    rw [accountRecord_jnames]; exact keysAC_nodup
  unfold Model.posted
  refine jrecAt_set (jrecAt_set (jrecAt_set h hac hnd (i := 2) (by rw [accountRecord_jnames]; rfl)
    (fun f hf => jfieldAt_set_num _ f hf)) (heap_setObj_self' hac) hnd (i := 8)
    (by rw [accountRecord_jnames]; rfl) (fun f hf => jfieldAt_set_num _ f hf))
    (heap_setObj_self' (heap_setObj_self' hac)) hnd (i := 9) (by rw [accountRecord_jnames]; rfl)
    (fun f hf => jfieldAt_set_num _ f hf)

/-! ## A write to the current account object keeps the loop's heap invariant -/

theorem ne_of_heap_plain_cls {σ : State} {a b : Addr} {c c' : ClassName}
    {fs fs' : List (FieldKey × Value)} (ha : σ.heap a = some (.plain c fs))
    (hb : σ.heap b = some (.plain c' fs')) (hc : c ≠ c') : a ≠ b := by
  intro e; subst e; rw [ha] at hb; cases hb; exact hc rfl

theorem tranOk_agree {σ σ' : State} {T : Addr} {W : List Addr} (h : TranOk σ T) (ha : Agree σ σ' W)
    (hn : NoStr σ W) (hT : T ∉ W) : TranOk σ' T := by
  obtain ⟨fs, h1, h2, ⟨d, s, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := h
  have hd : d ∉ W := fun hm => hn d hm s h4
  have hf : f ∉ W := fun hm => hn f hm _ h8
  exact ⟨fs, by rw [ha.2 T (State.lt_next_of_heap h1) hT, h1], h2,
    ⟨d, s, h3, by rw [ha.2 d (State.lt_next_of_heap h4) hd, h4], h5, h6⟩,
    ⟨f, h7, by rw [ha.2 f (State.lt_next_of_heap h8) hf, h8]⟩⟩

/-- Writing the account object `ac` (allocated by `run`, the one object the loop may write) keeps
the heap invariant. -/
theorem coreHeap_setObj_acct {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {ac : Addr}
    {fs : List (FieldKey × Value)} (hc : CoreHeap g σ0 σ h s [ac])
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fs)) (h0 : σ0.next ≤ ac) (o : Obj) :
    CoreHeap g σ0 (σ.setObj ac o) h s [ac] := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩ := hc
  have ha : Agree σ (σ.setObj ac o) [ac] :=
    agree_setObj_mem (agree_refl σ [ac]) (List.mem_singleton_self ac) o
  have hn : NoStr σ [ac] := by
    intro w hw st hst
    rw [List.mem_singleton] at hw
    subst hw
    rw [hac] at hst
    cases hst
  have hnot : ∀ x : Addr, x ≠ ac → x ∉ [ac] := fun x hx hm => hx (List.mem_singleton.1 hm)
  obtain ⟨fsR, hR, -⟩ := id hres
  obtain ⟨dxs, dm, hld, -⟩ := id hdisp
  obtain ⟨wxs, wm, hlw, -⟩ := id hw
  obtain ⟨rxs, rm, hlr, -⟩ := id hr
  obtain ⟨axs, hA, -⟩ := id ht
  obtain ⟨fsT, hT, -⟩ := id htr
  refine ⟨grows_setObj hg0 h0, inits_of_eq rfl hin, hfr,
    resAt_agree hres ha (hnot _ (ne_of_heap_plain_cls hR hac (by decide))),
    dispAt_agree hdisp ha hn (hnot _ (ne_of_heap_list_plain hld hac).symm),
    recsAt_agree hw ha hn (hnot _ (ne_of_heap_list_plain hlw hac).symm) (fun a hm => ?_),
    recsAt_agree hr ha hn (hnot _ (ne_of_heap_list_plain hlr hac).symm) (fun a hm => Or.inl hm),
    tableAt_agree ht ha hn (fun hm => ?_) (fun a hm => Or.inl hm),
    tranOk_agree htr ha hn (hnot _ (ne_of_heap_plain_cls hT hac (by decide))),
    jstrAt_agree hp ha hn, jstrAt_agree hcl ha hn⟩
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs' he => by rw [hac] at he; simp at he)
  · rw [List.mem_singleton] at hm
    subst hm
    rw [hac] at hA
    cases hA

/-! ## Machine arithmetic -/

theorem toInt_ofInt_of_range {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> omega

theorem toInt_ofNat_small {m : Nat} (hm : m < 4611686018427387904) :
    (BitVec.ofNat 64 m).toInt = (m : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

/-- `trunc (x + y, …)`: the sum of two longs in range, reduced modulo `m` towards zero. -/
theorem srem_add_mod (x y : Int) (m : Nat) (hm0 : 0 < m) (hm : m < 4611686018427387904)
    (hx1 : -4611686018427387904 ≤ x) (hx2 : x < 4611686018427387904)
    (hy1 : -4611686018427387904 ≤ y) (hy2 : y < 4611686018427387904) :
    (BitVec.ofInt 64 x + BitVec.ofInt 64 y).srem (BitVec.ofNat 64 m) =
      BitVec.ofInt 64 (Int.tmod (x + y) m) := by
  rw [← BitVec.ofInt_add]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, toInt_ofInt_of_range (by omega) (by omega), toInt_ofNat_small hm]
  have h1 := Int.tmod_lt_of_pos (x + y) (b := (m : Int)) (by omega)
  have h2 := Int.lt_tmod_of_pos (x + y) (b := (m : Int)) (by omega)
  rw [toInt_ofInt_of_range (by omega) (by omega)]

end EquivLean.Modernize.Cbact04c.Java
