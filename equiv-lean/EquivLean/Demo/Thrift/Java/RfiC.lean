import EquivLean.Demo.Thrift.Java.RfiD

/-!
# Thrift → Java (T4): `readFieldId(byte)`, the closers of its verification conditions

The body ends with `lastFieldId_ = id` (after `boolValue_ = Boolean.valueOf(..)` for the bool
nibbles 1 and 2); the long form first calls `readVarint32()` through its contract.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- `(short) (short) x = (short) x`. -/
theorem toShort_toShort (x : I32) : JInt.toShort (JInt.toShort x) = JInt.toShort x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [JInt.toShort, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
    BitVec.msb_eq_getLsbD_last]
  by_cases h : i < 16 <;> simp [h, hi]

/-- `σ'` differs from `σ` only at `p` and at new objects, and has `t`'s bytes. -/
def PStep (R : TRep) (σ σ' : State) (p t : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
  (∀ a, a < σ.next → a ≠ p → σ'.heap a = σ.heap a) ∧ R.src σ' t = R.src σ t ∧
  R.sink σ' t = R.sink σ t ∧ (∀ b, R.owns σ' t b ↔ R.owns σ t b)

theorem PStep.trans {R : TRep} {σ1 σ2 σ3 : State} {p t : Addr} (h1 : PStep R σ1 σ2 p t)
    (h2 : PStep R σ2 σ3 p t) : PStep R σ1 σ3 p t := by
  obtain ⟨n1, i1, s1, e1, r1, k1, o1⟩ := h1
  obtain ⟨n2, i2, s2, e2, r2, k2, o2⟩ := h2
  exact ⟨Nat.le_trans n1 n2, i2.trans i1, s2.trans s1,
    fun a ha hp => (e2 a (Nat.lt_of_lt_of_le ha n1) hp).trans (e1 a ha hp), r2.trans r1, k2.trans k1,
    fun b => (o2 b).trans (o1 b)⟩

/-- Replacing `p`'s object by one with the same `trans_` and `temp` keeps `CPAt`. -/
theorem cpAt_setp {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    {fs fs' : List (FieldKey × Value)} (h : CPAt P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (htr : Fields.get fs' (tpCls, "trans_") = Fields.get fs (tpCls, "trans_"))
    (hte : Fields.get fs' (cpCls, "temp") = Fields.get fs (cpCls, "temp")) :
    CPAt P R (σ.setObj p (.plain cpCls fs')) p t tmp ∧
      PStep R σ (σ.setObj p (.plain cpCls fs')) p t := by
  obtain ⟨fs0, xs, c, fst, hp0, htr0, hte0, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ := h
  rw [hp] at hp0
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp0
  subst hp0
  have hplt : p < σ.next := State.lt_next_of_heap hp
  obtain ⟨hinv', hsink, hsrc, -, -, -, how⟩ :=
    TRep.setObj_eq R (o := .plain cpCls fs') hinv hpt hop
  refine ⟨⟨fs', xs, c, fst, setObj_heap_self hplt, by rw [htr]; exact htr0,
    by rw [hte]; exact hte0, by rw [setObj_heap_ne (Ne.symm hptm)]; exact htm, hl,
    by rw [setObj_heap_ne (Ne.symm hpt)]; exact ht, hc1, hc2, hinv', hpt, htt, hptm,
    by rw [how]; exact hop, by rw [how]; exact hot⟩, ?_⟩
  exact ⟨Nat.le_of_eq (State.next_setObj σ p _).symm, rfl, rfl, fun a _ ha => setObj_heap_ne ha,
    hsrc, hsink, how⟩

/-- An allocation keeps `CPAt`. -/
theorem cpAt_alloc {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (o : Obj)
    (h : CPAt P R σ p t tmp) : CPAt P R (σ.alloc o).2 p t tmp ∧ PStep R σ (σ.alloc o).2 p t := by
  obtain ⟨fs0, xs, c, fst, hp0, htr0, hte0, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ := h
  have htlt := State.lt_next_of_heap ht
  obtain ⟨hinv', hsink, hsrc, -, -, -, how⟩ := TRep.alloc_eq R (o := o) hinv htlt
  refine ⟨⟨fs0, xs, c, fst, by rw [State.heap_alloc_of_lt (State.lt_next_of_heap hp0)]; exact hp0,
    htr0, hte0, by rw [State.heap_alloc_of_lt (State.lt_next_of_heap htm)]; exact htm, hl,
    by rw [State.heap_alloc_of_lt htlt]; exact ht, hc1, hc2, hinv', hpt, htt, hptm,
    by rw [how]; exact hop, by rw [how]; exact hot⟩, ?_⟩
  exact ⟨by rw [State.next_alloc]; exact Nat.le_succ _, rfl, rfl,
    fun a ha _ => State.heap_alloc_of_lt ha o, hsrc, hsink, how⟩

theorem get_set_trans (fs : List (FieldKey × Value)) (k : FieldKey) (v : Value)
    (h : (tpCls, "trans_") ≠ k) :
    Fields.get (Fields.set fs k v) (tpCls, "trans_") = Fields.get fs (tpCls, "trans_") := by
  rw [Fields.get_set, if_neg h]

theorem get_set_temp (fs : List (FieldKey × Value)) (k : FieldKey) (v : Value)
    (h : (cpCls, "temp") ≠ k) :
    Fields.get (Fields.set fs k v) (cpCls, "temp") = Fields.get fs (cpCls, "temp") := by
  rw [Fields.get_set, if_neg h]

/-- `lastFieldId_ = (short) x`. -/
theorem upd_last {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} (h : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (x : I32) :
    CPAt P R (σ.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_")
        (.int (JInt.toShort (JInt.toShort x)))))) p t tmp ∧
      PStep R σ (σ.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_")
        (.int (JInt.toShort (JInt.toShort x)))))) p t ∧
      LastAt (σ.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_")
        (.int (JInt.toShort (JInt.toShort x)))))) p (JInt.toShort x) := by
  obtain ⟨hC, hS⟩ := cpAt_setp h hp
    (get_set_trans fs (cpCls, "lastFieldId_") (.int (JInt.toShort (JInt.toShort x))) (by decide))
    (get_set_temp fs (cpCls, "lastFieldId_") (.int (JInt.toShort (JInt.toShort x))) (by decide))
  refine ⟨hC, hS, _, setObj_heap_self (State.lt_next_of_heap hp), ?_⟩
  rw [Fields.get_set, if_pos rfl, toShort_toShort]

/-- A bool type nibble: `boolValue_` set to a new `Boolean`. -/
theorem upd_bool {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} (h : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (o : Obj) :
    CPAt P R ((σ.alloc o).2.setObj p
        (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ.next)))) p t tmp ∧
      PStep R σ ((σ.alloc o).2.setObj p
        (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ.next)))) p t ∧
      ((σ.alloc o).2.setObj p
        (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ.next)))).heap p =
        some (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ.next))) := by
  obtain ⟨hC1, hS1⟩ := cpAt_alloc o h
  have hp1 : (σ.alloc o).2.heap p = some (.plain cpCls fs) := by
    rw [State.heap_alloc_of_lt (State.lt_next_of_heap hp)]; exact hp
  obtain ⟨hC2, hS2⟩ :=
    cpAt_setp hC1 hp1 (get_set_trans fs (cpCls, "boolValue_") (.ref σ.next) (by decide))
      (get_set_temp fs (cpCls, "boolValue_") (.ref σ.next) (by decide))
  exact ⟨hC2, hS1.trans hS2, setObj_heap_self (State.lt_next_of_heap hp1)⟩

theorem rframe_of_step {R : TRep} {σ σ' : State} {p t tmp : Addr} (h : PStep R σ σ' p t) :
    RFrame R σ σ' p t tmp :=
  ⟨h.1, h.2.1, h.2.2.1, fun a ha _ _ hp _ => h.2.2.2.1 a ha hp,
    fun a _ ho => by rw [h.2.2.2.2.2.2]; exact ho⟩

theorem rframe_of_call {R : TRep} {σ0 σ1 σ' : State} {p t tmp : Addr}
    (hn : σ0.next ≤ σ1.next) (hi : σ1.inits = σ0.inits) (hs : σ1.statics = σ0.statics)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom : OwnsMono R σ0 σ1 t) (h : PStep R σ1 σ' p t) : RFrame R σ0 σ' p t tmp :=
  ⟨Nat.le_trans hn h.1, h.2.1.trans hi, h.2.2.1.trans hs,
    fun a ha ht htm hp ho => (h.2.2.2.1 a (Nat.lt_of_lt_of_le ha hn) hp).trans (hh a ha ht htm ho),
    fun a ha ho => by rw [h.2.2.2.2.2.2]; exact hom a ha ho⟩

/-- The normal result, from the facts of the end state. -/
theorem rfiN_of {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {b last id : I32} {rest : Bytes}
    (hC0 : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : fieldIdJ last b (R.src σ t) = some (id, rest)) (hsrc : R.src σ' t = rest)
    (hsink : R.sink σ' t = R.sink σ t) (hL : LastAt σ' p id) (hC : CPAt P R σ' p t tmp)
    (hF : RFrame R σ σ' p t tmp) :
    rfiN P R [.ref p, .int b] σ (some (.int id)) σ' := by
  unfold rfiN
  intro p' t' tmp' fs' b' last' hargs hp' htr' hte' hlast'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  obtain ⟨rfl, rfl⟩ := cpAt_fields hC0 hp htr' hte'
  rw [hlast] at hlast'
  simp only [Option.some.injEq, Value.int.injEq] at hlast'
  subst hlast'
  exact ⟨id, rest, hf, rfl, hsrc, hsink, hL, hC, hF⟩

theorem fieldIdJ_short {last b : I32} {src : Bytes} (hm : ¬ modJ b = 0#32) :
    fieldIdJ last b src = some (JInt.toShort (last + modJ b), src) := by
  unfold fieldIdJ
  rw [if_pos (show modJ b ≠ 0#32 from hm)]

theorem fieldIdJ_long {last b : I32} {src rest : Bytes} {v : Nat} (hm : modJ b = 0#32)
    (hv : Spec.readVarint 5 src = some (v, rest)) :
    fieldIdJ last b src = some (JInt.toShort (uzzJ (BitVec.ofNat 32 v)), rest) := by
  unfold fieldIdJ
  rw [if_neg (show ¬ modJ b ≠ 0#32 from fun h => h hm), hv]
  rfl

/-- `σ1.heap p` after the `readVarint32()` call (`p` is not in the call's frame). -/
theorem heap_p_of_call {P : Program} {R : TRep} {σ σ1 : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} (hC : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hh : ∀ a, a < σ.next → a ≠ t → a ≠ tmp → ¬ R.owns σ t a → σ1.heap a = σ.heap a) :
    σ1.heap p = some (.plain cpCls fs) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpt, _, hptm, hop, _⟩ := hC
  rw [hh p (State.lt_next_of_heap hp) hpt hptm hop]
  exact hp

/-! ## The seven closers -/

/-- Short form, not a bool nibble. -/
theorem rfi_g7 {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {b last : I32} (hH : CPAtH P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hm : ¬ modJ b = 0#32) :
    rfiN P R [.ref p, .int b] σ (some (.int (JInt.toShort (last + modJ b))))
      (σ.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_")
        (.int (JInt.toShort (JInt.toShort (last + modJ b))))))) := by
  have hC := CPAtH.elim hH
  obtain ⟨hC', hS, hL⟩ := upd_last hC hp (last + modJ b)
  exact rfiN_of hC hp hlast (fieldIdJ_short hm) hS.2.2.2.2.1 hS.2.2.2.2.2.1 hL hC'
    (rframe_of_step hS)

/-- Short form, a bool nibble. -/
theorem rfi_g56 {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {b last : I32} {o : Obj} (hH : CPAtH P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hm : ¬ modJ b = 0#32) :
    rfiN P R [.ref p, .int b] σ (some (.int (JInt.toShort (last + modJ b))))
      (((σ.alloc o).2.setObj p
          (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ.next)))).setObj p
        (.plain cpCls (Fields.set (Fields.set fs (cpCls, "boolValue_") (.ref σ.next))
          (cpCls, "lastFieldId_") (.int (JInt.toShort (JInt.toShort (last + modJ b))))))) := by
  have hC := CPAtH.elim hH
  obtain ⟨hC1, hS1, hp1⟩ := upd_bool hC hp o
  obtain ⟨hC', hS, hL⟩ := upd_last hC1 hp1 (last + modJ b)
  have hS2 := hS1.trans hS
  exact rfiN_of hC hp hlast (fieldIdJ_short hm) hS2.2.2.2.2.1 hS2.2.2.2.2.2.1 hL hC'
    (rframe_of_step hS2)

/-- Long form, not a bool nibble. -/
theorem rfi_g3 {P : Program} {R : TRep} {σ σ1 : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {b last : I32} {v : Nat} (hH : CPAtH P R σ p t tmp)
    (hH1 : CPAtH P R σ1 p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hm : modJ b = 0#32)
    (hv : Spec.readVarint 5 (R.src σ t) = some (v, R.src σ1 t))
    (hsink : R.sink σ1 t = R.sink σ t)
    (hn : σ.next ≤ σ1.next) (hi : σ1.inits = σ.inits) (hs : σ1.statics = σ.statics)
    (hh : ∀ a, a < σ.next → a ≠ t → a ≠ tmp → ¬ R.owns σ t a → σ1.heap a = σ.heap a)
    (hom : OwnsMono R σ σ1 t) :
    rfiN P R [.ref p, .int b] σ (some (.int (JInt.toShort (uzzJ (BitVec.ofNat 32 v)))))
      (σ1.setObj p (.plain cpCls (Fields.set fs (cpCls, "lastFieldId_")
        (.int (JInt.toShort (JInt.toShort (uzzJ (BitVec.ofNat 32 v)))))))) := by
  have hC := CPAtH.elim hH
  have hp1 := heap_p_of_call hC hp hh
  obtain ⟨hC', hS, hL⟩ := upd_last (CPAtH.elim hH1) hp1 (uzzJ (BitVec.ofNat 32 v))
  exact rfiN_of hC hp hlast (fieldIdJ_long hm hv) hS.2.2.2.2.1 (hS.2.2.2.2.2.1.trans hsink) hL hC'
    (rframe_of_call hn hi hs hh hom hS)

/-- Long form, a bool nibble. -/
theorem rfi_g12 {P : Program} {R : TRep} {σ σ1 : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {b last : I32} {v : Nat} {o : Obj} (hH : CPAtH P R σ p t tmp)
    (hH1 : CPAtH P R σ1 p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hm : modJ b = 0#32)
    (hv : Spec.readVarint 5 (R.src σ t) = some (v, R.src σ1 t))
    (hsink : R.sink σ1 t = R.sink σ t)
    (hn : σ.next ≤ σ1.next) (hi : σ1.inits = σ.inits) (hs : σ1.statics = σ.statics)
    (hh : ∀ a, a < σ.next → a ≠ t → a ≠ tmp → ¬ R.owns σ t a → σ1.heap a = σ.heap a)
    (hom : OwnsMono R σ σ1 t) :
    rfiN P R [.ref p, .int b] σ (some (.int (JInt.toShort (uzzJ (BitVec.ofNat 32 v)))))
      (((σ1.alloc o).2.setObj p
          (.plain cpCls (Fields.set fs (cpCls, "boolValue_") (.ref σ1.next)))).setObj p
        (.plain cpCls (Fields.set (Fields.set fs (cpCls, "boolValue_") (.ref σ1.next))
          (cpCls, "lastFieldId_")
          (.int (JInt.toShort (JInt.toShort (uzzJ (BitVec.ofNat 32 v)))))))) := by
  have hC := CPAtH.elim hH
  have hp1 := heap_p_of_call hC hp hh
  obtain ⟨hC2, hS1, hp2⟩ := upd_bool (CPAtH.elim hH1) hp1 o
  obtain ⟨hC', hS, hL⟩ := upd_last hC2 hp2 (uzzJ (BitVec.ofNat 32 v))
  have hS2 := hS1.trans hS
  exact rfiN_of hC hp hlast (fieldIdJ_long hm hv) hS2.2.2.2.2.1 (hS2.2.2.2.2.2.1.trans hsink) hL hC'
    (rframe_of_call hn hi hs hh hom hS2)

/-- Long form, `readVarint32()` threw. -/
theorem rfi_g4 {P : Program} {R : TRep} {σ σ1 : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} {b last : I32} (hH : CPAtH P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hm : modJ b = 0#32)
    (hfwd : (Spec.VarintOverlong 5 (R.src σ t) ∧ ∃ fs, σ1.heap e = some (.plain tpeCls fs)) ∨
      (Spec.VarintTruncated 5 (R.src σ t) ∧ ∃ fs, σ1.heap e = some (.plain ttExcCls fs))) :
    rfiE P R [.ref p, .int b] σ e σ1 := by
  unfold rfiE
  intro p' t' tmp' fs' b' last' hargs hp' htr' hte' hlast'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  obtain ⟨rfl, rfl⟩ := cpAt_fields (CPAtH.elim hH) hp htr' hte'
  rw [hlast] at hlast'
  simp only [Option.some.injEq, Value.int.injEq] at hlast'
  subst hlast'
  refine ⟨?_, hfwd⟩
  unfold fieldIdJ
  rw [if_neg (show ¬ modJ b ≠ 0#32 from fun h => h hm),
    (Spec.readVarint_eq_none_iff 5 _).mpr (hfwd.imp (fun h => h.1) (fun h => h.1))]
  rfl

end EquivLean.Demo.Thrift.Java
