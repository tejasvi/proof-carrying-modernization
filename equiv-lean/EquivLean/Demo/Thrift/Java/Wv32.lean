import EquivLean.Demo.Thrift.Java.Lem

/-!
# Thrift → Java (T4): `TCompactProtocol.writeVarint32(int)` appends the varint (E)
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev wv32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeVarint32(int)».ref

/-- What `writeVarint32(n)` guarantees: it appends `varint (toU 32 n)` to the transport. -/
def wv32N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] → CPAt P R σ p t tmp →
    r = none ∧ CPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.varint n.toNat ∧
    R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

attribute [irreducible] wv32N

/-- **E for varint32**. -/
def wv32Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ CPAt P R σ p t tmp)
  (wv32N P R)
  (fun _ _ _ _ => False)

/-- Statement 3 (the loop head): the first `i` bytes of the varint are in `temp`, `n` holds the
rest `v`. -/
def wv32Inv : Invariants := [(3, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I32) (fs : List (FieldKey × Value)), args = [.ref p, .int n0] →
  σ0.heap p = some (.plain cpCls fs) → Fields.get fs (cpCls, "temp") = some (.ref tmp) →
  ∃ (i : Nat) (x : I32) (xs : List Value), fr.get 7 = some (.ref p) ∧
    fr.get 5 = some (.int x) ∧ fr.get 6 = some (.int (BitVec.ofNat 32 i)) ∧ i ≤ 4 ∧
    (i = 1 → x.toNat < 33554432) ∧ (i = 2 → x.toNat < 262144) ∧
    (i = 3 → x.toNat < 2048) ∧ (i = 4 → x.toNat < 16) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take i).map byteOf ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a))]

/-- The contract with a hidden copy of the protocol facts, for the proof. -/
def wv32SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp)
  (wv32N P R)
  (fun _ _ _ _ => False)

theorem wv32_entry {n0 : I32} {xs : List Value} : ∃ x, 0#32 = BitVec.ofNat 32 x ∧ x ≤ 4 ∧
    (x = 1 → BitVec.toNat n0 < 33554432) ∧ (x = 2 → BitVec.toNat n0 < 262144) ∧
    (x = 3 → BitVec.toNat n0 < 2048) ∧ (x = 4 → BitVec.toNat n0 < 16) ∧ (x = 0 ∨ xs = []) :=
  ⟨0, rfl, by omega, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), Or.inl rfl⟩

/-- The loop step: one more continuation byte. -/
theorem wv32_step {x n0 : I32} {i : Nat} {xs : List Value} {tmp : Addr} {σ0 : State}
    (hc : ¬ x &&& 4294967168#32 = 0#32) (hi : i ≤ 4) (h1 : i = 1 → x.toNat < 33554432)
    (h2 : i = 2 → x.toNat < 262144) (h3 : i = 3 → x.toNat < 2048) (h4 : i = 4 → x.toNat < 16)
    (hlen : xs.length = 16)
    (heq : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat) :
    ∃ i', BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 i' ∧ i' ≤ 4 ∧
      (i' = 1 → (JInt.ushr x 7#32).toNat < 33554432) ∧
      (i' = 2 → (JInt.ushr x 7#32).toNat < 262144) ∧
      (i' = 3 → (JInt.ushr x 7#32).toNat < 2048) ∧
      (i' = 4 → (JInt.ushr x 7#32).toNat < 16) ∧
      List.take i' ((List.map byteOf xs).set i
          (byteOf (.int (JInt.toByte (JInt.toByte (x &&& 127#32 ||| 128#32)))))) ++
        Spec.varint (JInt.ushr x 7#32).toNat = Spec.varint n0.toNat ∧
      ∀ a, ¬a = tmp → a = tmp →
        some (Obj.array (.prim .byte) (xs.set i (.int (JInt.toByte (JInt.toByte (x &&& 127#32 ||| 128#32)))))) =
          σ0.heap a := by
  have hge : ¬ x.toNat < 128 := fun h => hc ((and_m128_eq_zero x).mpr h)
  have hlt := x.isLt
  have hu := ushr7_toNat x
  refine ⟨i + 1, ofNat_succ32 i, by omega, by omega, by omega, by omega, by omega, ?_,
    fun a h1 h2 => absurd h2 h1⟩
  rw [List.map_take] at heq
  rw [hu, take_set_succ _ _ _ (by rw [List.length_map, hlen]; omega), byteOf_cont,
    List.append_assoc, List.singleton_append, ← heq, Spec.varint_eq x.toNat, if_neg hge]

/-- The call of `write` at the exit: its precondition. -/
theorem wv32_exit_pre (R : TRep) {σ0 σ : State} {t tmp : Addr} {xs : List Value} {i : Nat} {o : Value}
    (hinv : R.inv σ0 t) (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) (hnext : σ.next = σ0.next)
    (ht : tmp ≠ t) (ho : ¬ R.owns σ0 t tmp) (htl : tmp < σ.next) (hlen : xs.length = 16)
    (hi : i ≤ 4) :
    ∃ t' buf off len, (t = t' ∧ tmp = buf ∧ 0#32 = off ∧ BitVec.ofNat 32 i + 1#32 = len) ∧
      R.inv (σ.setObj tmp (.array (.prim .byte) (xs.set i o))) t' ∧
      ∃ x, (if buf = tmp then some (Obj.array (.prim .byte) (xs.set i o)) else σ0.heap buf) =
          some (.array (.prim .byte) x) ∧
        0 ≤ BitVec.toInt off ∧ 0 ≤ BitVec.toInt len ∧ BitVec.toInt off + BitVec.toInt len ≤ x.length ∧
        ¬buf = t' ∧ ¬R.owns (σ.setObj tmp (.array (.prim .byte) (xs.set i o))) t' buf := by
  obtain ⟨hinvσ, -, -, -, -, -, howσ⟩ := rep_scratch R hinv heq (Nat.le_of_eq hnext.symm) ht ho
  obtain ⟨hinv1, -, -, -, -, -, how1⟩ := R.setObj_eq (o := .array (.prim .byte) (xs.set i o)) hinvσ ht
    (by rw [howσ]; exact ho)
  refine ⟨t, tmp, 0#32, BitVec.ofNat 32 i + 1#32, ⟨rfl, rfl, rfl, rfl⟩, hinv1, xs.set i o,
    by rw [if_pos rfl], by decide, ?_, ?_, ht, by rw [how1, howσ]; exact ho⟩
  · rw [ofNat_succ32, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  · rw [show (0#32 : I32).toInt = 0 from rfl, ofNat_succ32, BitVec.toInt_eq_toNat_cond,
      BitVec.toNat_ofNat, List.length_set, hlen]
    split <;> omega

/-- The return: the transport got the varint. -/
theorem wv32_exit_post {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {n0 x : I32}
    {i : Nat} {xs : List Value}
    (hCP : CPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16) (hi : i < 16)
    (heqv : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat)
    (hexit : x &&& 4294967168#32 = 0#32)
    (hw : R.inv σ' t ∧
      R.sink σ' t = R.sink (σ.setObj tmp (.array (.prim .byte)
          (xs.set i (.int (JInt.toByte (JInt.toByte x)))))) t ++
        List.take (BitVec.toNat (BitVec.ofNat 32 i + 1#32)) (List.drop (BitVec.toNat 0#32)
          (List.map byteOf (xs.set i (.int (JInt.toByte (JInt.toByte x)))))) ∧
      R.src σ' t = R.src (σ.setObj tmp (.array (.prim .byte)
          (xs.set i (.int (JInt.toByte (JInt.toByte x)))))) t ∧
      TFrame R (σ.setObj tmp (.array (.prim .byte) (xs.set i (.int (JInt.toByte (JInt.toByte x)))))) σ' t t) :
    wv32N P R [.ref p, .int n0] σ0 none σ' := by
  unfold wv32N
  intro p' t' tmp' n' he hCP'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' hCP
  obtain ⟨hinv', hsink, hsrc, hf⟩ := hw
  have hCPσ : CPAt P R σ p t tmp := cpAt_scratch hCP hheap (Nat.le_of_eq hnext.symm) htmpσ hlen
  obtain ⟨fs, xs0, c, fst, hph, -, -, htmh, -, -, -, -, hinv0, hpt, htt, hptm, hop, hot⟩ := hCP
  have htl : tmp < σ.next := State.lt_next_of_heap htmpσ
  have hCP1 : CPAt P R (σ.setObj tmp (.array (.prim .byte) (xs.set i (.int (JInt.toByte (JInt.toByte x)))))) p t tmp :=
    cpAt_scratch hCPσ (fun a ha => setObj_heap_ne ha) (by rw [State.next_setObj]; exact Nat.le_refl _)
      (setObj_heap_self htl) (by rw [List.length_set]; exact hlen)
  obtain ⟨hCP', hfr⟩ := cpAt_call hCP1 hf hinv' hpt htt
  obtain ⟨-, hs0, hr0, -, -, -, how0⟩ := rep_scratch R hinv0 hheap (Nat.le_of_eq hnext.symm) htt hot
  obtain ⟨-, hs1, hr1, -, -, -, how1⟩ := R.setObj_eq
    (o := .array (.prim .byte) (xs.set i (.int (JInt.toByte (JInt.toByte x))))) (rep_scratch R hinv0 hheap (Nat.le_of_eq hnext.symm) htt hot).1 htt
    (by rw [how0]; exact hot)
  have hx : x.toNat < 128 := (and_m128_eq_zero x).mp hexit
  have hi1 : BitVec.toNat (BitVec.ofNat 32 i + 1#32) = i + 1 := by
    rw [ofNat_succ32, BitVec.toNat_ofNat]
    omega
  obtain ⟨hn', hin', hst', -, -, -⟩ := hf
  refine ⟨rfl, hCP', ?_, by rw [hsrc, hr1, hr0], ?_, ?_, ?_, ?_⟩
  · rw [List.map_take] at heqv
    rw [hsink, hs1, hs0, hi1, show BitVec.toNat 0#32 = 0 from rfl, List.drop_zero, List.map_set,
      take_set_succ _ _ _ (by rw [List.length_map, hlen]; omega), toByte_toByte, byteOf_toByte,
      ← heqv, Spec.varint_eq x.toNat, if_pos hx]
  · rw [State.next_setObj] at hn'
    rw [← hnext]
    exact hn'
  · rw [hin']
    exact hin
  · rw [hst']
    exact hst
  · intro a ha hat hatm hao
    rw [hfr a (by rw [State.next_setObj, hnext]; exact ha) hat (by rw [how1, how0]; exact hao) hat,
      setObj_heap_ne hatm, hheap a hatm]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem wv32_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    wv32Ref (fun P => wv32SpecI P R) wv32Inv 60 := by
  jverify_body [Contains, tContracts, CPAt, PFrame, wv32SpecI, wv32Inv, writeSpec, writeSig, ttCls,
    cpCls, tpCls]
  case left => exact wv32_entry
  case right.isFalse.isTrue => exact wv32_step ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.isTrue.isTrue.isFalse.some.some.true.left =>
    exact wv32_exit_pre R ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.isTrue.isTrue.isFalse.some.some.true.right.normal =>
    rename_i hw
    exact wv32_exit_post (CPAtH.elim ‹CPAtH _ R _ _ _ _›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (by
        obtain ⟨-, h1, h2, h3, h4⟩ := hw _ _ _ _ _ rfl rfl rfl rfl (by rw [if_pos rfl])
        exact ⟨h1, h2, h3, h4⟩)

end EquivLean.Demo.Thrift.Java
