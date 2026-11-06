import EquivLean.Demo.Thrift.Java.RfbD

/-!
# Thrift → Java (T4): `readFieldBegin()`, the closers of its verification conditions
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## The byte read, as a Java `byte` -/

theorem sx_toNat_mod256 (u : UInt8) : (BitVec.signExtend 32 u.toBitVec).toNat % 256 = u.toNat := by
  have h := congrArg BitVec.toNat (setWidth8_signExtend32 u.toBitVec)
  rw [BitVec.toNat_setWidth] at h
  exact h

theorem sx_toNat_mod16 (u : UInt8) : (BitVec.signExtend 32 u.toBitVec).toNat % 16 = u.toNat % 16 := by
  rw [← sx_toNat_mod256 u, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 256)]

theorem sx_toNat_and15 (u : UInt8) :
    (BitVec.signExtend 32 u.toBitVec).toNat &&& 15 = u.toNat % 16 := by
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact sx_toNat_mod16 u

theorem sx_ne_zero {u : UInt8} (h : ¬ BitVec.signExtend 32 u.toBitVec = 0#32) : u.toNat ≠ 0 := by
  intro h0
  apply h
  have : u.toBitVec = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    exact h0
  rw [this]
  decide

theorem toNat_of_sx_eq_zero {u : UInt8} (h : BitVec.signExtend 32 u.toBitVec = 0#32) :
    u.toNat = 0 := by
  have := sx_toNat_mod256 u
  rw [h] at this
  rw [← this]
  rfl

theorem ttypeOfCompact_le {n tt : Nat} (h : Spec.ttypeOfCompact n = some tt) : tt ≤ 16 := by
  unfold Spec.ttypeOfCompact at h
  split at h <;> cases h <;> decide

theorem fieldIdJ_toShort {last b id : I32} {src rest : Bytes}
    (h : fieldIdJ last b src = some (id, rest)) : JInt.toShort id = id := by
  unfold fieldIdJ at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, toShort_toShort]
  · cases hv : Spec.readVarint 5 src with
    | none => rw [hv] at h; cases h
    | some q =>
      rw [hv] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, toShort_toShort]

/-! ## Writes to an object outside the protocol and transport objects -/

/-- Writing an object `a` that `t` does not use (not `p`, `t`, `tmp`) keeps `CPAt` and `t`'s
representation. -/
theorem cpAt_setOther {P : Program} {R : TRep} {σ : State} {p t tmp a : Addr} (o : Obj)
    (h : CPAt P R σ p t tmp) (hap : a ≠ p) (hat : a ≠ t) (hatm : a ≠ tmp) (ho : ¬ R.owns σ t a) :
    CPAt P R (σ.setObj a o) p t tmp ∧ R.src (σ.setObj a o) t = R.src σ t ∧
      R.sink (σ.setObj a o) t = R.sink σ t ∧ (∀ b, R.owns (σ.setObj a o) t b ↔ R.owns σ t b) := by
  obtain ⟨fs, xs, c, fst, hp, htr, hte, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ := h
  obtain ⟨hinv', hsink, hsrc, -, -, -, how⟩ := TRep.setObj_eq R (o := o) hinv hat ho
  refine ⟨⟨fs, xs, c, fst, by rw [setObj_heap_ne (Ne.symm hap)]; exact hp, htr, hte,
    by rw [setObj_heap_ne (Ne.symm hatm)]; exact htm, hl, by rw [setObj_heap_ne (Ne.symm hat)]; exact ht,
    hc1, hc2, hinv', hpt, htt, hptm, by rw [how]; exact hop, by rw [how]; exact hot⟩, hsrc, hsink, how⟩

/-! ## The closers -/

/-- The byte 0: the static `TSTOP`. -/
theorem rfb_g1 {P : Program} {R : TRep} {σ0 σ1 : State} {p t tmp : Addr} {u : UInt8}
    (hH0 : CPAtH P R σ0 p t tmp) (hH1 : CPAtH P R σ1 p t tmp)
    (hsink : R.sink σ1 t = R.sink σ0 t) (hn : σ0.next ≤ σ1.next) (hi : σ1.inits = σ0.inits)
    (hs : σ1.statics = σ0.statics)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom : OwnsMono R σ0 σ1 t)
    (hsrc : R.src σ0 t = u :: R.src σ1 t) (hu : BitVec.signExtend 32 u.toBitVec = 0#32) :
    rfbN P R [.ref p] σ0 (some ((σ0.static (cpCls, "TSTOP")).getD .null)) σ1 := by
  unfold rfbN
  intro p' t' tmp' fs last hargs hp htr hte hlast
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  have hC0 := CPAtH.elim hH0
  obtain ⟨h1, h2⟩ := cpAt_fields hC0 hp htr hte
  subst t' tmp'
  have hp1 := heap_p_of_call hC0 hp hh
  exact ⟨u, R.src σ1 t, hsrc, hsink, CPAtH.elim hH1,
    ⟨hn, hi, hs, fun a ha hat hatm _ hao => hh a ha hat hatm hao, hom⟩,
    Or.inl ⟨toNat_of_sx_eq_zero hu, rfl, rfl, fs, hp1, hlast⟩⟩

/-- `getTType(type & 0x0F)`: its precondition (a known type nibble). -/
theorem rfb_g2 {R : TRep} {σ0 σ1 : State} {t : Addr} {u : UInt8} (p : Addr)
    (hnib : NibbleOK (R.src σ0 t)) (hsrc : R.src σ0 t = u :: R.src σ1 t)
    (hu : ¬ BitVec.signExtend 32 u.toBitVec = 0#32) :
    ∃ p' b, (p = p' ∧ BitVec.signExtend 32 u.toBitVec &&& 15#32 = b) ∧
      (Spec.ttypeOfCompact (b.toNat % 16)).isSome = true := by
  refine ⟨p, _, ⟨rfl, rfl⟩, ?_⟩
  rw [and15_toNat, Nat.mod_mod, sx_toNat_mod16]
  exact hnib u _ hsrc (sx_ne_zero hu)

/-- `getTType` threw: impossible on a known type nibble. -/
theorem rfb_g4 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t e : Addr} {u : UInt8}
    (hnib : NibbleOK (R.src σ0 t)) (hsrc : R.src σ0 t = u :: R.src σ1 t)
    (hu : ¬ BitVec.signExtend 32 u.toBitVec = 0#32)
    (hn : Spec.ttypeOfCompact (((BitVec.signExtend 32 u.toBitVec).toNat &&& 15) % 16) = none) :
    rfbE P R [.ref p] σ0 e σ' := by
  rw [sx_toNat_and15, Nat.mod_mod] at hn
  have h := hnib u _ hsrc (sx_ne_zero hu)
  rw [hn] at h
  exact absurd h (by decide)

/-- `readByte()` threw: no byte. -/
theorem rfb_g5 {P : Program} {R : TRep} {σ0 σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hH0 : CPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = [])
    (hexc : σ'.heap e = some (.plain ttExcCls w)) : rfbE P R [.ref p] σ0 e σ' := by
  unfold rfbE
  intro p' t' tmp' fs last hargs hp htr hte _
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp htr hte
  subst t' tmp'
  exact Or.inl ⟨hsrc, w, hexc⟩

/-- `readFieldId(type)` threw: the long-form id is not a varint of at most 5 bytes. -/
theorem rfb_g8 {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} {last : I32} {u : UInt8}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlast0 : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : fieldIdJ last (BitVec.signExtend 32 u.toBitVec) (R.src σ1 t) = none)
    (hsrc : R.src σ0 t = u :: R.src σ1 t) (hu : u.toNat ≠ 0)
    (hexc : (Spec.VarintOverlong 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
      (Spec.VarintTruncated 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))) :
    rfbE P R [.ref p] σ0 e σ' := by
  unfold rfbE
  intro p' t' tmp' fs' last' hargs hp htr hte hlast
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlast0] at hlast
  simp only [Option.some.injEq, Value.int.injEq] at hlast
  subst hlast
  exact Or.inr ⟨u, R.src σ1 t, hsrc, hu, hf, hexc⟩

/-- `CPAt`'s subclass fact in the form the symbolic execution leaves. -/
theorem isSub_fold {P : Program} {c d : ClassName} (h : P.isSubclass c d = some true) :
    ∃ a, P.supersN (4095 + 1) c = some a ∧ d ∈ a := by
  unfold Program.isSubclass Program.supers at h
  obtain ⟨a, ha, hc⟩ := Option.map_eq_some_iff.mp h
  exact ⟨a, ha, List.contains_iff_mem.mp hc⟩

/-- The call `readFieldId(type)`: its precondition's transport facts. -/
theorem rfb_g6 {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} {Q : ClassName → Prop}
    (hH : CPAtH P R σ p t tmp) (hconv : ∀ c, P.isSubclass c ttCls = some true → Q c) :
    ∃ x, σ.heap tmp = some (.array (.prim .byte) x) ∧ x.length = 16 ∧
      ∃ c, (∃ f, σ.heap t = some (.plain c f)) ∧ (P.findClass c).isSome = true ∧ Q c ∧
        R.inv σ t ∧ ¬ R.owns σ t p ∧ ¬ R.owns σ t tmp := by
  obtain ⟨fs, xs, c, fst, hp, htr, hte, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ :=
    CPAtH.elim hH
  exact ⟨xs, htm, hl, c, ⟨fst, ht⟩, hc1, hconv c hc2, hinv, hop, hot⟩

/-- At the cut (statement 8): the invariant, after `new TField` and `getTType`. -/
theorem rfb_g3 {P : Program} {R : TRep} {σ0 σ1 : State} {p t tmp : Addr} {u : UInt8} {w : Nat}
    (hH0 : CPAtH P R σ0 p t tmp) (hH1 : CPAtH P R σ1 p t tmp)
    (hsink : R.sink σ1 t = R.sink σ0 t) (hn : σ0.next ≤ σ1.next)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom : OwnsMono R σ0 σ1 t)
    (hu : ¬ BitVec.signExtend 32 u.toBitVec = 0#32)
    (htt : Spec.ttypeOfCompact (((BitVec.signExtend 32 u.toBitVec).toNat &&& 15) % 16) = some w) :
    ∃ u', (u = u' ∧ R.src σ1 t = R.src (σ1.alloc tfNew).2 t) ∧ ¬ u'.toNat = 0 ∧
      ∃ x, Spec.ttypeOfCompact (u'.toNat % 16) = some x ∧
        BitVec.signExtend 32 u.toBitVec = BitVec.signExtend 32 u'.toBitVec ∧
        BitVec.ofNat 32 w = BitVec.ofNat 32 x ∧ ¬ p = σ1.next ∧
        CPAtH P R (σ1.alloc tfNew).2 p t tmp ∧ ¬ σ1.next = t ∧ ¬ σ1.next = tmp ∧ ¬ σ1.next = p ∧
        ¬ R.owns (σ1.alloc tfNew).2 t σ1.next ∧ R.sink (σ1.alloc tfNew).2 t = R.sink σ0 t ∧
        σ0.next ≤ σ1.next + 1 ∧
        (∀ a, a < σ0.next → ¬ a = t → ¬ a = tmp → ¬ R.owns σ0 t a →
          (if a = σ1.next then some tfNew else σ1.heap a) = σ0.heap a) ∧
        OwnsMono R σ0 (σ1.alloc tfNew).2 t := by
  have hC1 := CPAtH.elim hH1
  obtain ⟨_, _, _, _, hp0, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := CPAtH.elim hH0
  obtain ⟨_, _, _, _, hp1, _, _, htm1, _, ht1, _, _, hinv1, _, _, _, _, _⟩ := CPAtH.elim hH1
  have hplt0 := State.lt_next_of_heap hp0
  have hplt1 := State.lt_next_of_heap hp1
  have htmlt1 := State.lt_next_of_heap htm1
  have htlt1 := State.lt_next_of_heap ht1
  obtain ⟨_, hsink', hsrc', _, _, _, how⟩ := TRep.alloc_eq R (o := tfNew) hinv1 htlt1
  refine ⟨u, ⟨rfl, hsrc'.symm⟩, sx_ne_zero hu, w, ?_, rfl, rfl,
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hplt0 hn), CPAtH.intro (cpAt_alloc tfNew hC1).1,
    (Nat.ne_of_lt htlt1).symm, (Nat.ne_of_lt htmlt1).symm, (Nat.ne_of_lt hplt1).symm, ?_,
    by rw [hsink', hsink], Nat.le_succ_of_le hn, ?_, ?_⟩
  · rwa [sx_toNat_and15, Nat.mod_mod] at htt
  · rw [how]
    intro h
    exact Nat.lt_irrefl _ (R.inv_owns σ1 t _ hinv1 h).1
  · intro a ha hat hatm hao
    rw [if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le ha hn))]
    exact hh a ha hat hatm hao
  · intro a ha hao
    rw [how]
    exact hom a ha hao

theorem tf_get_type (L : List (FieldKey × Value)) (v1 v2 v3 : Value) :
    Fields.get (Fields.set (Fields.set (Fields.set L (tfCls, "name") v1) (tfCls, "type") v2)
      (tfCls, "id") v3) (tfCls, "type") = some v2 := by
  rw [Fields.get_set, if_neg (show ¬ ((tfCls, "type") : FieldKey) = (tfCls, "id") by decide),
    Fields.get_set, if_pos rfl]

theorem tf_get_id (L : List (FieldKey × Value)) (v1 v2 v3 : Value) :
    Fields.get (Fields.set (Fields.set (Fields.set L (tfCls, "name") v1) (tfCls, "type") v2)
      (tfCls, "id") v3) (tfCls, "id") = some v3 := by
  rw [Fields.get_set, if_pos rfl]

/-- After `readFieldId` and the `TField` constructor: the result. -/
theorem rfb_g7 {P : Program} {R : TRep} {σ0 σ1 σc : State} {p t tmp r0 : Addr}
    {fs w : List (FieldKey × Value)} {last id : I32} {u : UInt8} {tt : Nat}
    {so o1 o2 : Obj} {F : List (FieldKey × Value)}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlast0 : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hHc : CPAtH P R σc p t tmp) (hpc : σc.heap p = some (.plain cpCls w))
    (hlastc : Fields.get w (cpCls, "lastFieldId_") = some (.int id))
    (hsinkc : R.sink σc t = R.sink σ1 t)
    (hhc : ∀ a, a < σ1.next → a ≠ t → a ≠ tmp → a ≠ p → ¬ R.owns σ1 t a → σc.heap a = σ1.heap a)
    (hnc : σ1.next ≤ σc.next) (hic : σc.inits = σ1.inits) (hsc : σc.statics = σ1.statics)
    (homc : OwnsMono R σ1 σc t)
    (hf : fieldIdJ last (BitVec.signExtend 32 u.toBitVec) (R.src σ1 t) = some (id, R.src σc t))
    (hsrc : R.src σ0 t = u :: R.src σ1 t) (hu : u.toNat ≠ 0)
    (htt : Spec.ttypeOfCompact (u.toNat % 16) = some tt)
    (hr0 : σ1.heap r0 = some tfNew) (hr0t : r0 ≠ t) (hr0tm : r0 ≠ tmp) (hr0p : r0 ≠ p)
    (hown1 : ¬ R.owns σ1 t r0) (hr0n : σ0.next ≤ r0)
    (hsink1 : R.sink σ1 t = R.sink σ0 t) (hn1 : σ0.next ≤ σ1.next) (hi1 : σ1.inits = σ0.inits)
    (hs1 : σ1.statics = σ0.statics)
    (hh1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom1 : OwnsMono R σ0 σ1 t)
    (hFt : Fields.get F (tfCls, "type") = some (.int (JInt.toByte (BitVec.ofNat 32 tt))))
    (hFi : Fields.get F (tfCls, "id") = some (.int (JInt.toShort id))) :
    rfbN P R [.ref p] σ0 (some (.ref r0))
      ((((σc.alloc so).2.setObj r0 o1).setObj r0 o2).setObj r0 (.plain tfCls F)) := by
  have hr0lt : r0 < σ1.next := State.lt_next_of_heap hr0
  have hr0c : r0 < σc.next := Nat.lt_of_lt_of_le hr0lt hnc
  have hownc : ¬ R.owns σc t r0 := homc r0 hr0lt hown1
  have hCc := CPAtH.elim hHc
  have hplc : p < σc.next := State.lt_next_of_heap hpc
  obtain ⟨hCa, hSa⟩ := cpAt_alloc so hCc
  have hownA : ¬ R.owns (σc.alloc so).2 t r0 := by rw [hSa.2.2.2.2.2.2]; exact hownc
  obtain ⟨hC1, hsrc1, hsink1', how1⟩ := cpAt_setOther o1 hCa hr0p hr0t hr0tm hownA
  have hown1' : ¬ R.owns ((σc.alloc so).2.setObj r0 o1) t r0 := by rw [how1]; exact hownA
  obtain ⟨hC2, hsrc2, hsink2, how2⟩ := cpAt_setOther o2 hC1 hr0p hr0t hr0tm hown1'
  have hown2 : ¬ R.owns (((σc.alloc so).2.setObj r0 o1).setObj r0 o2) t r0 := by
    rw [how2]; exact hown1'
  obtain ⟨hC3, hsrc3, hsink3, how3⟩ := cpAt_setOther (.plain tfCls F) hC2 hr0p hr0t hr0tm hown2
  have hnf : (((σc.alloc so).2.setObj r0 o1).setObj r0 o2).next = σc.next + 1 := by
    simp only [State.next_setObj, State.next_alloc]
  have hheap : ∀ a, a ≠ r0 → a < σc.next →
      ((((σc.alloc so).2.setObj r0 o1).setObj r0 o2).setObj r0 (.plain tfCls F)).heap a = σc.heap a := by
    intro a ha hac
    rw [setObj_heap_ne ha, setObj_heap_ne ha, setObj_heap_ne ha, State.heap_alloc_of_lt hac]
  have httl : tt < 128 := Nat.lt_of_le_of_lt (ttypeOfCompact_le htt) (by decide)
  unfold rfbN
  intro p' t' tmp' fs' last' hargs hp htr hte hlast
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlast0] at hlast
  simp only [Option.some.injEq, Value.int.injEq] at hlast
  subst hlast
  refine ⟨u, R.src σ1 t, hsrc, ?_, hC3, ⟨?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨hu, tt, id, R.src σc t, r0, F, htt, hf,
    ?_, rfl, setObj_heap_self (by rw [hnf]; exact Nat.lt_succ_of_lt hr0c), ?_, ?_, w, ?_, hlastc⟩⟩
  · rw [hsink3, hsink2, hsink1', hSa.2.2.2.2.2.1, hsinkc, hsink1]
  · rw [State.next_setObj, hnf]; exact Nat.le_succ_of_le (Nat.le_trans hn1 hnc)
  · exact hic.trans hi1
  · exact hsc.trans hs1
  · intro a ha hat hatm hap hao
    have har0 : a ≠ r0 := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha hr0n)
    rw [hheap a har0 (Nat.lt_of_lt_of_le ha (Nat.le_trans hn1 hnc)),
      hhc a (Nat.lt_of_lt_of_le ha hn1) hat hatm hap (hom1 a ha hao), hh1 a ha hat hatm hao]
  · intro a ha hao
    rw [how3, how2, how1, hSa.2.2.2.2.2.2]
    exact homc a (Nat.lt_of_lt_of_le ha hn1) (hom1 a ha hao)
  · rw [hsrc3, hsrc2, hsrc1, hSa.2.2.2.2.1]
  · rw [hFt, toByte_ofNat_lt httl]
  · rw [hFi, fieldIdJ_toShort hf]
  · rw [hheap p (Ne.symm hr0p) hplc]; exact hpc

end EquivLean.Demo.Thrift.Java
