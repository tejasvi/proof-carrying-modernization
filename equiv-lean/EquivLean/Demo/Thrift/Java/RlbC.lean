import EquivLean.Demo.Thrift.Java.RlbD

/-!
# Thrift → Java (T4): `readListBegin()`, the closers of its verification conditions
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem shr4_sx_fin : ∀ n : Fin 256,
    JInt.shr (BitVec.signExtend 32 (UInt8.ofNat n).toBitVec) 4#32 &&& 15#32 =
      BitVec.ofNat 32 ((UInt8.ofNat n).toNat / 16) := by
  decide +kernel

/-- The size nibble of a header byte, as Java computes it. -/
theorem shr4_sx (u : UInt8) :
    JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = BitVec.ofNat 32 (u.toNat / 16) := by
  have h := shr4_sx_fin ⟨u.toNat, u.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

theorem hi15_of {u : UInt8} (h : JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32) :
    u.toNat / 16 = 15 := by
  rw [shr4_sx] at h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have := u.toNat_lt
  omega

theorem hi15_not {u : UInt8} (h : ¬ JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32) :
    u.toNat / 16 ≠ 15 := by
  intro h15
  apply h
  rw [shr4_sx, h15]

theorem listSizeJ_long {u : UInt8} {rest rest' : Bytes} {v : Nat} (h15 : u.toNat / 16 = 15)
    (h : Spec.readVarint 5 rest = some (v, rest')) :
    listSizeJ u rest = some (BitVec.ofNat 32 v, rest') := by
  simp [listSizeJ, h15, h]

theorem listSizeJ_none {u : UInt8} {rest : Bytes} (h15 : u.toNat / 16 = 15)
    (h : Spec.readVarint 5 rest = none) : listSizeJ u rest = none := by
  simp [listSizeJ, h15, h]

theorem listSizeJ_short {u : UInt8} {rest : Bytes} (h15 : u.toNat / 16 ≠ 15) :
    listSizeJ u rest = some (BitVec.ofNat 32 (u.toNat / 16), rest) := by
  simp [listSizeJ, h15]

theorem tl_get_elemType (L : List (FieldKey × Value)) (v1 v2 : Value) :
    Fields.get (Fields.set (Fields.set L (tlCls, "elemType") v1) (tlCls, "size") v2) (tlCls, "elemType") =
      some v1 := by
  rw [Fields.get_set, if_neg (show ¬ ((tlCls, "elemType") : FieldKey) = (tlCls, "size") by decide),
    Fields.get_set, if_pos rfl]

theorem tl_get_size (L : List (FieldKey × Value)) (v1 v2 : Value) :
    Fields.get (Fields.set (Fields.set L (tlCls, "elemType") v1) (tlCls, "size") v2) (tlCls, "size") =
      some v2 := by
  rw [Fields.get_set, if_pos rfl]

/-! ## The closers -/

/-- The cut at statement 2: the byte read has a known type nibble. -/
theorem rlb_nib {src rest : Bytes} {u : UInt8} (hn : NibbleOKL src) (hs : src = u :: rest) :
    (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := hn u rest hs

/-- `readByte()` threw: no byte. -/
theorem rlb_rb_exc {P : Program} {R : TRep} {σ0 σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hH0 : CPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = [])
    (hexc : σ'.heap e = some (.plain ttExcCls w)) : rlbE P R [.ref p] σ0 e σ' := by
  unfold rlbE
  intro p' t' tmp' fs lim hargs hp htr hte _
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp htr hte
  subst t' tmp'
  exact Or.inl ⟨hsrc, w, hexc⟩

/-- `readVarint32()` threw: the long-form size is not a varint of at most 5 bytes. -/
theorem rlb_rv32_exc {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp e : Addr} {u : UInt8}
    (hH0 : CPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = u :: R.src σ1 t)
    (hcond : JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32)
    (hexc : (Spec.VarintOverlong 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
      (Spec.VarintTruncated 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))) :
    rlbE P R [.ref p] σ0 e σ' := by
  have hnone : listSizeJ u (R.src σ1 t) = none :=
    listSizeJ_none (hi15_of hcond) ((Spec.readVarint_eq_none_iff 5 _).mpr (hexc.imp And.left And.left))
  unfold rlbE
  intro p' t' tmp' fs lim hargs hp htr hte _
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp htr hte
  subst t' tmp'
  exact Or.inr (Or.inl ⟨u, R.src σ1 t, hsrc, hnone, hexc⟩)

/-- The cut at statement 7 from the short form (`(size_and_type >> 4) & 15 ≠ 15`). -/
theorem rlb_cut7_short {R : TRep} {σ0 σ : State} {t tmp : Addr} {u : UInt8}
    (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true)
    (hcond : ¬ JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a) :
    ∃ u' rest, (u = u' ∧ R.src σ t = rest) ∧ ∃ x, listSizeJ u' rest = some (x, R.src σ t) ∧
      (Spec.ttypeOfCompact (u'.toNat % 16)).isSome = true ∧
      BitVec.signExtend 32 u.toBitVec = BitVec.signExtend 32 u'.toBitVec ∧
      JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = x ∧
      ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a := by
  refine ⟨u, R.src σ t, ⟨rfl, rfl⟩, JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32, ?_,
    hnib, rfl, rfl, hh⟩
  rw [listSizeJ_short (hi15_not hcond), shr4_sx]

/-- The cut at statement 7 from the long form: the varint after the byte. -/
theorem rlb_cut7_long {P : Program} {R : TRep} {σ0 σ1 σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {u : UInt8} {v : Nat}
    (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true)
    (hcond : JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32)
    (hp1 : σ1.heap p = some (.plain cpCls fs)) (hH1 : CPAtH P R σ1 p t tmp)
    (hn1 : σ0.next ≤ σ1.next)
    (hh1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom1 : OwnsMono R σ0 σ1 t)
    (hrv : Spec.readVarint 5 (R.src σ1 t) = some (v, R.src σ t))
    (hn2 : σ1.next ≤ σ.next)
    (hh2 : ∀ a, a < σ1.next → a ≠ t → a ≠ tmp → ¬R.owns σ1 t a → σ.heap a = σ1.heap a)
    (hom2 : OwnsMono R σ1 σ t) :
    ∃ u' rest, (u = u' ∧ R.src σ1 t = rest) ∧ ∃ x, listSizeJ u' rest = some (x, R.src σ t) ∧
      (Spec.ttypeOfCompact (u'.toNat % 16)).isSome = true ∧
      BitVec.signExtend 32 u.toBitVec = BitVec.signExtend 32 u'.toBitVec ∧ BitVec.ofNat 32 v = x ∧
      σ.heap p = some (.plain cpCls fs) ∧ σ0.next ≤ σ.next ∧
      (∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t := by
  refine ⟨u, R.src σ1 t, ⟨rfl, rfl⟩, BitVec.ofNat 32 v, listSizeJ_long (hi15_of hcond) hrv, hnib, rfl,
    rfl, heap_p_of_call (CPAtH.elim hH1) hp1 hh2, Nat.le_trans hn1 hn2, ?_, ?_⟩
  · intro a ha hat hatm hao
    rw [hh2 a (Nat.lt_of_lt_of_le ha hn1) hat hatm (hom1 a ha hao), hh1 a ha hat hatm hao]
  · intro a ha hao
    exact hom2 a (Nat.lt_of_lt_of_le ha hn1) (hom1 a ha hao)

/-- `getTType`'s precondition: a known type nibble. -/
theorem rlb_gtt_pre {u : UInt8} (p : Addr) (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true) :
    ∃ p' b, (p = p' ∧ BitVec.signExtend 32 u.toBitVec = b) ∧
      (Spec.ttypeOfCompact (b.toNat % 16)).isSome = true :=
  ⟨p, _, ⟨rfl, rfl⟩, by rw [sx_toNat_mod16]; exact hnib⟩

/-- `getTType` threw: impossible on a known type nibble. -/
theorem rlb_gtt_exc {P : Program} {R : TRep} {σ0 σ' : State} {p e : Addr} {u : UInt8}
    (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true)
    (hn : Spec.ttypeOfCompact ((BitVec.signExtend 32 u.toBitVec).toNat % 16) = none) :
    rlbE P R [.ref p] σ0 e σ' := by
  rw [sx_toNat_mod16] at hn
  rw [hn] at hnib
  exact absurd hnib (by decide)

/-- `checkContainerReadLength` threw: a negative size or one above the limit. -/
theorem rlb_ccrl_exc {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp e : Addr}
    {fs w : List (FieldKey × Value)} {lim : I64} {u : UInt8} {rest : Bytes} {size : I32}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlim0 : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hsrc0 : R.src σ0 t = u :: rest) (hsz : listSizeJ u rest = some (size, R.src σ t))
    (hc : size.toInt < 0 ∨ ¬ InLimit lim size) (hexc : σ'.heap e = some (.plain tpeCls w)) :
    rlbE P R [.ref p] σ0 e σ' := by
  unfold rlbE
  intro p' t' tmp' fs' lim' hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlim0] at hlim
  simp only [Option.some.injEq, Value.long.injEq] at hlim
  subst hlim
  exact Or.inr (Or.inr (Or.inl ⟨u, rest, size, R.src σ t, hsrc0, hsz, hc, w, hexc⟩))

theorem minSize_byte {tt : Nat} (htt : tt ≤ 16) :
    (JInt.toByte (BitVec.ofNat 32 tt)).toNat = tt := by
  rw [toByte_ofNat_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `checkReadBytesAvailable` threw: `getMinSerializedSize` does not list the element type. -/
theorem rlb_crba_exc {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp e : Addr}
    {fs w L : List (FieldKey × Value)} {lim : I64} {u : UInt8} {rest : Bytes} {size : I32} {tt : Nat}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlim0 : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hsrc0 : R.src σ0 t = u :: rest) (hsz : listSizeJ u rest = some (size, R.src σ t))
    (h0 : 0 ≤ size.toInt) (hin : InLimit lim size)
    (htt : Spec.ttypeOfCompact ((BitVec.signExtend 32 u.toBitVec).toNat % 16) = some tt)
    (hms : ∀ (lfs : List (FieldKey × Value)) (b : I32),
      Fields.set (Fields.set L (tlCls, "elemType") (.int (JInt.toByte (BitVec.ofNat 32 tt))))
        (tlCls, "size") (.int size) = lfs →
      Fields.get lfs (tlCls, "elemType") = some (.int b) → minSize b.toNat = none)
    (hexc : σ'.heap e = some (.plain ttExcCls w)) :
    rlbE P R [.ref p] σ0 e σ' := by
  have hn := hms _ _ rfl (tl_get_elemType _ _ _)
  rw [minSize_byte (ttypeOfCompact_le htt)] at hn
  unfold rlbE
  intro p' t' tmp' fs' lim' hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlim0] at hlim
  simp only [Option.some.injEq, Value.long.injEq] at hlim
  subst hlim
  rw [sx_toNat_mod16] at htt
  exact Or.inr (Or.inr (Or.inr ⟨u, rest, size, R.src σ t, tt, hsrc0, hsz, h0, hin, htt, hn, w, hexc⟩))

/-- The return: the new `TList`. -/
theorem rlb_post {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr}
    {fs F : List (FieldKey × Value)} {lim : I64} {u : UInt8} {rest : Bytes} {size : I32} {tt : Nat}
    {so o1 : Obj}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlim0 : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hsrc0 : R.src σ0 t = u :: rest) (hsz : listSizeJ u rest = some (size, R.src σ t))
    (hH : CPAtH P R σ p t tmp) (hsink : R.sink σ t = R.sink σ0 t) (hn : σ0.next ≤ σ.next)
    (hi : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a)
    (hom : OwnsMono R σ0 σ t) (h0 : 0 ≤ size.toInt) (hin : InLimit lim size)
    (htt : Spec.ttypeOfCompact ((BitVec.signExtend 32 u.toBitVec).toNat % 16) = some tt)
    (hFt : Fields.get F (tlCls, "elemType") = some (.int (JInt.toByte (BitVec.ofNat 32 tt))))
    (hFs : Fields.get F (tlCls, "size") = some (.int size))
    (hms : ∀ (lfs : List (FieldKey × Value)) (b : I32), F = lfs →
      Fields.get lfs (tlCls, "elemType") = some (.int b) → (minSize b.toNat).isSome = true) :
    rlbN P R [.ref p] σ0 (some (.ref σ.next))
      (((σ.alloc so).2.setObj σ.next o1).setObj σ.next (.plain tlCls F)) := by
  obtain ⟨fs1, xs1, c1, fst1, hp1, -, -, htm1, -, ht1, -, -, hinv1, -, -, -, -, -⟩ := CPAtH.elim hH
  have hlp : σ.next ≠ p := Nat.ne_of_gt (State.lt_next_of_heap hp1)
  have hlt : σ.next ≠ t := Nat.ne_of_gt (State.lt_next_of_heap ht1)
  have hltm : σ.next ≠ tmp := Nat.ne_of_gt (State.lt_next_of_heap htm1)
  have hownS : ¬ R.owns σ t σ.next := fun h => Nat.lt_irrefl _ (R.inv_owns σ t σ.next hinv1 h).1
  obtain ⟨hCa, hSa⟩ := cpAt_alloc so (CPAtH.elim hH)
  have hownA : ¬ R.owns (σ.alloc so).2 t σ.next := by rw [hSa.2.2.2.2.2.2]; exact hownS
  obtain ⟨hC1, hsrc1, hsink1, how1⟩ := cpAt_setOther o1 hCa hlp hlt hltm hownA
  have hown1 : ¬ R.owns ((σ.alloc so).2.setObj σ.next o1) t σ.next := by rw [how1]; exact hownA
  obtain ⟨hC2, hsrc2, hsink2, how2⟩ := cpAt_setOther (.plain tlCls F) hC1 hlp hlt hltm hown1
  have hown2 : ¬ R.owns (((σ.alloc so).2.setObj σ.next o1).setObj σ.next (.plain tlCls F)) t σ.next := by
    rw [how2]; exact hown1
  have hnf : ((σ.alloc so).2.setObj σ.next o1).next = σ.next + 1 := by
    simp only [State.next_setObj, State.next_alloc]
  have hheap : ∀ a, a ≠ σ.next → a < σ.next →
      (((σ.alloc so).2.setObj σ.next o1).setObj σ.next (.plain tlCls F)).heap a = σ.heap a := by
    intro a ha hac
    rw [setObj_heap_ne ha, setObj_heap_ne ha, State.heap_alloc_of_lt hac]
  have hle := ttypeOfCompact_le htt
  have hbt : JInt.toByte (BitVec.ofNat 32 tt) = BitVec.ofNat 32 tt := toByte_ofNat_lt (by omega)
  obtain ⟨k, hk⟩ : ∃ k, minSize tt = some k := by
    have h := hms F _ rfl hFt
    rw [minSize_byte hle] at h
    exact Option.isSome_iff_exists.mp h
  unfold rlbN
  intro p' t' tmp' fs' lim' hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlim0] at hlim
  simp only [Option.some.injEq, Value.long.injEq] at hlim
  subst hlim
  rw [sx_toNat_mod16] at htt
  refine ⟨u, rest, size, R.src σ t, tt, k, σ.next, F, hsrc0, hsz, h0, hin, htt, hk,
    by rw [hsrc2, hsrc1, hSa.2.2.2.2.1], by rw [hsink2, hsink1, hSa.2.2.2.2.2.1, hsink], hC2, rfl,
    setObj_heap_self (by rw [hnf]; exact Nat.lt_succ_self _), by rw [hFt, hbt], hFs, hn, hlt, hltm,
    hlp, hown2, ⟨?_, hi, hst, ?_⟩, ?_⟩
  · rw [State.next_setObj, hnf]
    exact Nat.le_succ_of_le hn
  · intro a ha hat hatm hao
    have hal : a < σ.next := Nat.lt_of_lt_of_le ha hn
    rw [hheap a (Nat.ne_of_lt hal) hal, hh a ha hat hatm hao]
  · intro a ha hao
    rw [how2, how1, hSa.2.2.2.2.2.2]
    exact hom a ha hao

/-- `checkReadBytesAvailable(list)`'s precondition, after `new TList` and its constructor. -/
theorem rlb_crba_pre {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} {so o1 : Obj}
    {F : List (FieldKey × Value)} {X : Addr → Option Obj} {b s : I32}
    (hH : CPAtH P R σ p t tmp)
    (hFt : Fields.get F (tlCls, "elemType") = some (.int b))
    (hFs : Fields.get F (tlCls, "size") = some (.int s)) :
    ∃ p' l, (p = p' ∧ σ.next = l) ∧
      (∃ x x_1, CPAtH P R (((σ.alloc so).2.setObj σ.next o1).setObj σ.next (.plain tlCls F)) p' x x_1) ∧
      ∃ x, (if l = σ.next then some (Obj.plain tlCls F) else X l) = some (.plain tlCls x) ∧
        (∃ x_1, Fields.get x (tlCls, "elemType") = some (.int x_1)) ∧
        ∃ x_1, Fields.get x (tlCls, "size") = some (.int x_1) := by
  obtain ⟨fs1, xs1, c1, fst1, hp1, -, -, htm1, -, ht1, -, -, hinv1, -, -, -, -, -⟩ := CPAtH.elim hH
  have hlp : σ.next ≠ p := Nat.ne_of_gt (State.lt_next_of_heap hp1)
  have hlt : σ.next ≠ t := Nat.ne_of_gt (State.lt_next_of_heap ht1)
  have hltm : σ.next ≠ tmp := Nat.ne_of_gt (State.lt_next_of_heap htm1)
  have hownS : ¬ R.owns σ t σ.next := fun h => Nat.lt_irrefl _ (R.inv_owns σ t σ.next hinv1 h).1
  obtain ⟨hCa, hSa⟩ := cpAt_alloc so (CPAtH.elim hH)
  have hownA : ¬ R.owns (σ.alloc so).2 t σ.next := by rw [hSa.2.2.2.2.2.2]; exact hownS
  obtain ⟨hC1, -, -, how1⟩ := cpAt_setOther o1 hCa hlp hlt hltm hownA
  have hown1 : ¬ R.owns ((σ.alloc so).2.setObj σ.next o1) t σ.next := by rw [how1]; exact hownA
  obtain ⟨hC2, -, -, -⟩ := cpAt_setOther (.plain tlCls F) hC1 hlp hlt hltm hown1
  exact ⟨p, σ.next, ⟨rfl, rfl⟩, ⟨t, tmp, CPAtH.intro hC2⟩, F, if_pos rfl, ⟨b, hFt⟩, ⟨s, hFs⟩⟩

end EquivLean.Demo.Thrift.Java
