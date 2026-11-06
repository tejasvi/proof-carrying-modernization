import EquivLean.Demo.Thrift.Java.WfD
import EquivLean.Demo.Thrift.Java.Zz

/-!
# Thrift → Java (T4): the field header writer, the closers of its verification conditions
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## `writeByteDirect(byte)` -/

/-- The call `write(temp, 0, 1)`: its precondition. -/
theorem wbd_pre (R : TRep) {σ0 : State} {t tmp : Addr} {xs : List Value} {o : Value}
    (hinv : R.inv σ0 t) (ht : tmp ≠ t) (ho : ¬ R.owns σ0 t tmp) (hlen : xs.length = 16) :
    ∃ t' buf off len, (t = t' ∧ tmp = buf ∧ (0#32 : I32) = off ∧ (1#32 : I32) = len) ∧
      R.inv (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 o))) t' ∧
      ∃ x, (if buf = tmp then some (Obj.array (.prim .byte) (xs.set 0 o)) else σ0.heap buf) =
          some (.array (.prim .byte) x) ∧
        0 ≤ BitVec.toInt off ∧ 0 ≤ BitVec.toInt len ∧ BitVec.toInt off + BitVec.toInt len ≤ x.length ∧
        ¬buf = t' ∧ ¬R.owns (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 o))) t' buf := by
  obtain ⟨hinv1, -, -, -, -, -, how1⟩ := R.setObj_eq (o := .array (.prim .byte) (xs.set 0 o)) hinv ht ho
  refine ⟨t, tmp, 0#32, 1#32, ⟨rfl, rfl, rfl, rfl⟩, hinv1, xs.set 0 o, by rw [if_pos rfl], by decide,
    by decide, ?_, ht, by rw [how1]; exact ho⟩
  rw [List.length_set, hlen]
  decide

theorem take1_set0 {xs : List Value} (hlen : xs.length = 16) (v : Value) :
    List.take (BitVec.toNat (1#32 : I32)) (List.drop (BitVec.toNat (0#32 : I32))
      (List.map byteOf (xs.set 0 v))) = [byteOf v] := by
  cases xs with
  | nil => simp at hlen
  | cons x xs' => rfl

/-- The return: the byte appended. -/
theorem wbd_post {P : Program} {R : TRep} {σ0 σ' : State} {p t tmp : Addr} {b : I32}
    {xs : List Value} (hH : CPAtH P R σ0 p t tmp)
    (htm : σ0.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (hw : R.inv σ' t ∧
      R.sink σ' t = R.sink (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 (.int (JInt.toByte b))))) t ++
        List.take (BitVec.toNat (1#32 : I32)) (List.drop (BitVec.toNat (0#32 : I32))
          (List.map byteOf (xs.set 0 (.int (JInt.toByte b))))) ∧
      R.src σ' t = R.src (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 (.int (JInt.toByte b))))) t ∧
      TFrame R (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 (.int (JInt.toByte b))))) σ' t t) :
    wbdN P R [.ref p, .int b] σ0 none σ' := by
  have hCP := CPAtH.elim hH
  have htl : tmp < σ0.next := State.lt_next_of_heap htm
  obtain ⟨fs0, xs0, c, fst, hph, -, -, htmh, -, -, -, -, hinv0, hpt, htt, hptm, hop, hot⟩ := CPAtH.elim hH
  have hCP1 : CPAt P R (σ0.setObj tmp (.array (.prim .byte) (xs.set 0 (.int (JInt.toByte b))))) p t tmp :=
    cpAt_scratch hCP (fun a ha => setObj_heap_ne ha) (by rw [State.next_setObj]; exact Nat.le_refl _)
      (setObj_heap_self htl) (by rw [List.length_set]; exact hlen)
  obtain ⟨hinv', hsink, hsrc, hf⟩ := hw
  obtain ⟨hCP', hfr⟩ := cpAt_call hCP1 hf hinv' hpt htt
  obtain ⟨-, hs1, hr1, -, -, -, how1⟩ :=
    R.setObj_eq (o := .array (.prim .byte) (xs.set 0 (.int (JInt.toByte b)))) hinv0 htt hot
  obtain ⟨hn', hin', hst', -, hown', -⟩ := hf
  have hplt : p < σ0.next := State.lt_next_of_heap hph
  unfold wbdN
  intro p' t' tmp' fs b' he hp htr hte
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨h1, h2⟩ := he
  subst p' b'
  obtain ⟨h3, h4⟩ := cpAt_fields hCP hp htr hte
  subst t' tmp'
  refine ⟨rfl, ?_, by rw [hsrc, hr1], CPAtH.intro hCP', ?_, ⟨?_, hin', hst', ?_⟩, ?_⟩
  · rw [hsink, hs1, take1_set0 hlen, byteOf_toByte]
  · rw [hfr p (by rw [State.next_setObj]; exact hplt) hpt (by rw [how1]; exact hop) hpt,
      setObj_heap_ne hptm]
    exact hp
  · rw [State.next_setObj] at hn'
    exact hn'
  · intro a ha hat hatm hao
    rw [hfr a (by rw [State.next_setObj]; exact ha) hat (by rw [how1]; exact hao) hat,
      setObj_heap_ne hatm]
  · intro a ha hao
    exact hown' a (by rw [State.next_setObj]; exact ha) (by rw [how1]; exact hao)

/-! ## `writeI16(short)` -/

theorem wi16_post {P : Program} {R : TRep} {σ0 σ' : State} {p t tmp : Addr} {i : I32}
    (hH : CPAtH P R σ0 p t tmp) (hH' : CPAtH P R σ' p t tmp)
    (hsink : R.sink σ' t = R.sink σ0 t ++ Spec.varint (BitVec.toNat (JInt.shl i 1#32 ^^^ JInt.shr i 31#32)))
    (hsrc : R.src σ' t = R.src σ0 t) (hn : σ0.next ≤ σ'.next) (hi : σ'.inits = σ0.inits)
    (hs : σ'.statics = σ0.statics)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ'.heap a = σ0.heap a) :
    wi16N P R [.ref p, .int i] σ0 none σ' := by
  have hC := CPAtH.elim hH
  unfold wi16N
  intro p' t' tmp' fs i' he hp htr hte
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨h1, h2⟩ := he
  subst p' i'
  obtain ⟨h3, h4⟩ := cpAt_fields hC hp htr hte
  subst t' tmp'
  exact ⟨rfl, by rw [hsink, zz32_val], hsrc, hH', heap_p_of_call hC hp hh, hn, hi, hs, hh⟩

/-! ## `writeFieldBeginInternal` -/

theorem short_range {x : I32} (h : JInt.toShort x = x) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  rw [← h]
  unfold JInt.toShort
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  exact ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩

/-- `id - last` in `int`, for `short`s: no wrap. -/
theorem sub_bmod {id last ty : I32} (hW : Hide (WfbFacts id last ty)) :
    (id.toInt - last.toInt).bmod 4294967296 = id.toInt - last.toInt := by
  obtain ⟨h1, h2, -⟩ := Hide.elim hW
  have r1 := short_range h1
  have r2 := short_range h2
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The type override `-1` is excluded. -/
theorem wfb_neg1 {id last : I32} (hW : Hide (WfbFacts id last 4294967295#32)) : False :=
  absurd (Hide.elim hW).2.2 (by decide)

/-- `field` after the two calls of the long form. -/
theorem wfb_heap_f {R : TRep} {σ0 σ1 σ2 : State} {t tmp f : Addr} {o : Obj}
    (hf0 : σ0.heap f = some o)
    (hh1 : ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hh2 : ∀ a, a < σ1.next → ¬a = t → ¬a = tmp → ¬R.owns σ1 t a → σ2.heap a = σ1.heap a)
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfo : ¬ R.owns σ0 t f)
    (hom : OwnsMono R σ0 σ1 t) (hn : σ0.next ≤ σ1.next) : σ2.heap f = some o := by
  have hflt : f < σ0.next := State.lt_next_of_heap hf0
  rw [hh2 f (Nat.lt_of_lt_of_le hflt hn) hft hftm (hom f hflt hfo), hh1 f hflt hft hftm hfo, hf0]

/-- The objects outside the two calls' frames. -/
theorem wfb_heap_a {R : TRep} {σ0 σ1 σ2 : State} {t tmp a : Addr}
    (hh1 : ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hh2 : ∀ a, a < σ1.next → ¬a = t → ¬a = tmp → ¬R.owns σ1 t a → σ2.heap a = σ1.heap a)
    (hom : OwnsMono R σ0 σ1 t) (hn : σ0.next ≤ σ1.next)
    (ha : a < σ0.next) (hat : a ≠ t) (hatm : a ≠ tmp) (hao : ¬ R.owns σ0 t a) :
    σ2.heap a = σ0.heap a := by
  rw [hh2 a (Nat.lt_of_lt_of_le ha hn) hat hatm (hom a ha hao), hh1 a ha hat hatm hao]

/-- The long form, `id ≤ last`. -/
theorem wfb_bytes_le {id last ty : I32} (hc : id.toInt ≤ last.toInt) :
    UInt8.ofNat ty.toNat :: Spec.varint (Spec.zigzag id.toInt) =
      Spec.fieldHeader last.toInt id.toInt ty.toNat :=
  (Spec.fieldHeader_long (by omega)).symm

/-- The long form, `id - last > 15`. -/
theorem wfb_bytes_gt {id last ty : I32} (hW : Hide (WfbFacts id last ty))
    (hc2 : 15 < (id.toInt - last.toInt).bmod 4294967296) :
    UInt8.ofNat ty.toNat :: Spec.varint (Spec.zigzag id.toInt) =
      Spec.fieldHeader last.toInt id.toInt ty.toNat := by
  rw [sub_bmod hW] at hc2
  exact (Spec.fieldHeader_long (by omega)).symm

/-- The short form: the byte `(id - last) << 4 | ty`. -/
theorem wfb_bytes_short {id last ty : I32} (hW : Hide (WfbFacts id last ty))
    (hc1 : ¬ id.toInt ≤ last.toInt) (hc2 : ¬ 15 < (id.toInt - last.toInt).bmod 4294967296) :
    [UInt8.ofNat (JInt.toByte (JInt.shl (id - last) 4#32 ||| ty)).toNat] =
      Spec.fieldHeader last.toInt id.toInt ty.toNat := by
  rw [sub_bmod hW] at hc2
  obtain ⟨h1, h2, hty⟩ := Hide.elim hW
  have hd : 1 ≤ id.toInt - last.toInt ∧ id.toInt - last.toInt ≤ 15 := by omega
  rw [Spec.fieldHeader_short hd hty]
  have hsub : id - last = BitVec.ofNat 32 (id.toInt - last.toInt).toNat := by
    apply BitVec.toInt_inj.mp
    rw [BitVec.toInt_sub, sub_bmod hW, BitVec.toInt_ofNat', Int.toNat_of_nonneg (by omega),
      Int.bmod_eq_of_le (by omega) (by omega)]
  have hdl : (id.toInt - last.toInt).toNat < 16 := by omega
  have hv : JInt.shl (id - last) 4#32 ||| ty =
      BitVec.ofNat 32 (16 * (id.toInt - last.toInt).toNat + ty.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, hsub, JInt.shl, BitVec.toNat_shiftLeft,
      show (4#32 : I32).toNat % 32 = 4 from rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (id.toInt - last.toInt).toNat < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show (id.toInt - last.toInt).toNat <<< 4 < 2 ^ 32 by
        rw [Nat.shiftLeft_eq]; omega),
      Spec.shl4_or _ hty, Nat.mod_eq_of_lt (by omega)]
  have hb := byteOf_toByte (BitVec.ofNat 32 (16 * (id.toInt - last.toInt).toNat + ty.toNat))
  simp only [byteOf] at hb
  rw [hv, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- From `label3`: `lastFieldId_ = id`, return. -/
theorem wfb_exit {P : Program} {R : TRep} {σ0 σ : State} {p t tmp f : Addr}
    {fs ffs : List (FieldKey × Value)} {ty id last : I32}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlast0 : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf0 : σ0.heap f = some (.plain tfCls ffs)) (hid0 : Fields.get ffs (tfCls, "id") = some (.int id))
    (hW : Hide (WfbFacts id last ty))
    (hp : σ.heap p = some (.plain cpCls fs)) (hH : CPAtH P R σ p t tmp)
    (hsink : R.sink σ t = R.sink σ0 t ++ Spec.fieldHeader last.toInt id.toInt ty.toNat)
    (hsrc : R.src σ t = R.src σ0 t) (hn : σ0.next ≤ σ.next) (hi : σ.inits = σ0.inits)
    (hs : σ.statics = σ0.statics)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) :
    wfbN P R [.ref p, .ref f, .int ty] σ0 none
      (σ.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_") (.int (JInt.toShort id))))) := by
  have hC0 := CPAtH.elim hH0
  obtain ⟨hC', hS⟩ := cpAt_setp (CPAtH.elim hH) hp
    (get_set_trans fs (cpCls, "lastFieldId_") (.int (JInt.toShort id)) (by decide))
    (get_set_temp fs (cpCls, "lastFieldId_") (.int (JInt.toShort id)) (by decide))
  have hplt : p < σ.next := State.lt_next_of_heap hp
  have hids : JInt.toShort id = id := (Hide.elim hW).1
  unfold wfbN
  intro p' t' tmp' f' fs' ffs' ty' id' last' he hp' htr hte hlast hf hid
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨h1, h2, h3⟩ := he
  subst p' f' ty'
  rw [hp0] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  obtain ⟨h4, h5⟩ := cpAt_fields hC0 hp0 htr hte
  subst t' tmp'
  rw [hlast0] at hlast
  simp only [Option.some.injEq, Value.int.injEq] at hlast
  subst hlast
  rw [hf0] at hf
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hf
  subst hf
  rw [hid0] at hid
  simp only [Option.some.injEq, Value.int.injEq] at hid
  subst hid
  refine ⟨rfl, by rw [hS.2.2.2.2.2.1, hsink], by rw [hS.2.2.2.2.1, hsrc], hC', ?_,
    ⟨Nat.le_trans hn hS.1, hS.2.1.trans hi, hS.2.2.1.trans hs, ?_⟩⟩
  · refine ⟨_, setObj_heap_self hplt, ?_⟩
    rw [Fields.get_set, if_pos rfl, hids]
  · intro a ha hat hatm hap hao
    rw [setObj_heap_ne hap, hh a ha hat hatm hao]

end EquivLean.Demo.Thrift.Java
