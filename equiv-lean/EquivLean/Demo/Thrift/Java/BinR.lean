import EquivLean.Demo.Thrift.Java.BinW
import EquivLean.Demo.Thrift.Java.Byte

/-!
# Thrift → Java (T4): `TBinaryProtocol.readI16/readI32` read the big-endian bytes (D, M)

Each reader takes the buffer fast path (`getBytesRemainingInBuffer() ≥ k`: the bytes at
`getBufferPosition()` in `getBuffer()`, then `consumeBuffer(k)`) or `readAll(inoutTemp, 0, k)`, then
combines `buf[off] … buf[off + k - 1]`. One cut point, at `label2` (statement 15): the `k` bytes at
`buf[off …]` are the source's next `k` bytes. `readI64` (the same proof, eight bytes) is in `BinR64`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- What a binary reader leaves of the protocol object, the transport and the heap (to rebuild
`BPAt` and `PFrame` at its return). -/
def RdFrame (R : TRep) (σ0 σ : State) (p t tmp : Addr) : Prop :=
  R.inv σ t ∧ R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧
  σ.statics = σ0.statics ∧ σ.heap p = σ0.heap p ∧
  (∃ xs, σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16) ∧
  (∀ c fst, σ0.heap t = some (.plain c fst) → ∃ fst', σ.heap t = some (.plain c fst')) ∧
  ¬ R.owns σ t p ∧ ¬ R.owns σ t tmp ∧
  (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a)

/-! ## Bytes to values -/

theorem bits255 : ∀ i, i < 32 → (255#32).getLsbD i = decide (i < 8) := by decide

/-- A byte read from the wire, `& 0xFF`: its unsigned value. -/
theorem sx_and255 (u : UInt8) : BitVec.signExtend 32 u.toBitVec &&& 255#32 = BitVec.ofNat 32 u.toNat := by
  have hu := u.toNat_lt
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, getLsbD_sx, bits255 i hi, BitVec.getLsbD_ofNat]
  by_cases h8 : i < 8
  · simp [hi, h8]
  · have : u.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h8, this]

theorem byte_and255 (u : UInt8) :
    JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 255#32 = BitVec.ofNat 32 u.toNat := by
  rw [toShort_sx, sx_and255]

theorem shl_ofNat32 (a s : Nat) (hs : s < 32) (h : a * 2 ^ s < 2 ^ 32) :
    JInt.shl (BitVec.ofNat 32 a) (BitVec.ofNat 32 s) = BitVec.ofNat 32 (a * 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.shl, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have ha : a < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right a (Nat.two_pow_pos s)) h
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ha,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- Two values whose bits do not overlap: `|` adds them. -/
theorem or_ofNat32 (a b s : Nat) (hb : b < 2 ^ s) (h : a * 2 ^ s + b < 2 ^ 32) :
    BitVec.ofNat 32 (a * 2 ^ s) ||| BitVec.ofNat 32 b = BitVec.ofNat 32 (a * 2 ^ s + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a * 2 ^ s < 2 ^ 32), Nat.mod_eq_of_lt (by omega : b < 2 ^ 32),
    Nat.mod_eq_of_lt h, Nat.mul_comm a, ← Nat.two_pow_add_eq_or_of_lt hb]

theorem toShort_ofNat_toInt (m : Nat) :
    (JInt.toShort (BitVec.ofNat 32 m)).toInt = Spec.toS 16 m := by
  simp only [JInt.toShort]
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.setWidth_ofNat_of_le (by decide), BitVec.toInt_ofNat']
  rfl

/-- The value `readI16()` computes from the two bytes. -/
theorem ri16_val (u0 u1 : UInt8) :
    (JInt.toShort (JInt.shl (JInt.toShort (BitVec.signExtend 32 u0.toBitVec) &&& 255#32) 8#32 |||
      JInt.toShort (BitVec.signExtend 32 u1.toBitVec) &&& 255#32)).toInt =
      Spec.toS 16 (256 * u0.toNat + u1.toNat) := by
  have h0 := u0.toNat_lt
  have h1 := u1.toNat_lt
  rw [byte_and255, byte_and255, shl_ofNat32 u0.toNat 8 (by decide) (by omega),
    or_ofNat32 u0.toNat u1.toNat 8 (by omega) (by omega), toShort_ofNat_toInt]
  congr 1
  omega

/-! ## The paths of a reader -/

/-- The call `readAll(inoutTemp, 0, k)`: its precondition. -/
theorem br_readAll_pre (R : TRep) {σ : State} {t tmp : Addr} {xs : List Value} {k : Nat}
    (hinv : R.inv σ t) (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (ht : tmp ≠ t) (ho : ¬ R.owns σ t tmp) (hk : k ≤ 16) :
    ∃ t' buf off len, (t = t' ∧ tmp = buf ∧ (0#32 : I32) = off ∧ BitVec.ofNat 32 k = len) ∧ R.inv σ t' ∧
      ∃ x, σ.heap buf = some (.array (.prim .byte) x) ∧ 0 ≤ BitVec.toInt off ∧ 0 ≤ BitVec.toInt len ∧
        BitVec.toInt off + BitVec.toInt len ≤ (x.length : Int) ∧ ¬buf = t' ∧ ¬R.owns σ t' buf := by
  refine ⟨t, tmp, 0#32, BitVec.ofNat 32 k, ⟨rfl, rfl, rfl, rfl⟩, hinv, xs, htmp, by decide, ?_, ?_, ht, ho⟩
  · rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  · rw [show (0#32 : I32).toInt = 0 from rfl, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, hlen]
    split <;> omega

/-- The reader's frame after `readAll` (the slow path). -/
theorem rdFrame_slow {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {c : ClassName}
    {f0 f1 : List (FieldKey × Value)} {xs : List Value}
    (hBP : BPAtH P R σ0 p t tmp) (hsink : R.sink σ t = R.sink σ0 t) (ht0 : σ0.heap t = some (.plain c f0))
    (hinv : R.inv σ t) (hown : ∀ a, a < σ0.next → ¬R.owns σ0 t a → ¬R.owns σ t a)
    (ht1 : σ.heap t = some (.plain c f1))
    (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hxs : xs.length = 16)
    (hfr : ∀ a, a < σ0.next → ¬a = t → ¬R.owns σ0 t a → ¬a = tmp → σ.heap a = σ0.heap a)
    (hnext : σ0.next ≤ σ.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics) :
    RdFrame R σ0 σ p t tmp := by
  obtain ⟨fs, xs0, c0, fst, hph, -, -, htmh, -, hth, -, -, -, hpt, htt, hptm, hop, hot⟩ := BPAtH.elim hBP
  have hplt : p < σ0.next := State.lt_next_of_heap hph
  have htlt : tmp < σ0.next := State.lt_next_of_heap htmh
  refine ⟨hinv, hsink, hnext, hin, hst, hfr p hplt hpt hop hptm, ⟨xs, htmp, hxs⟩, ?_, hown p hplt hop,
    hown tmp htlt hot, fun a ha hat hatm hao => hfr a ha hat hao hatm⟩
  intro c' fst' h'
  rw [ht0] at h'
  simp only [Option.some.injEq, Obj.plain.injEq] at h'
  obtain ⟨rfl, -⟩ := h'
  exact ⟨f1, ht1⟩

/-- The reader's frame after `consumeBuffer` (the fast path). -/
theorem rdFrame_fast {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {c : ClassName}
    {f0 f1 : List (FieldKey × Value)}
    (hBP : BPAtH P R σ0 p t tmp) (hsink : R.sink σ t = R.sink σ0 t) (ht0 : σ0.heap t = some (.plain c f0))
    (hinv : R.inv σ t) (hheap : ∀ a, ¬a = t → σ.heap a = σ0.heap a) (hown : ∀ a, R.owns σ t a ↔ R.owns σ0 t a)
    (ht1 : σ.heap t = some (.plain c f1))
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics) :
    RdFrame R σ0 σ p t tmp := by
  obtain ⟨fs, xs0, c0, fst, hph, -, -, htmh, hl, hth, -, -, -, hpt, htt, hptm, hop, hot⟩ := BPAtH.elim hBP
  refine ⟨hinv, hsink, Nat.le_of_eq hnext.symm, hin, hst, hheap p hpt, ⟨xs0, by rw [hheap tmp htt]; exact htmh, hl⟩,
    ?_, by rw [hown]; exact hop, by rw [hown]; exact hot, fun a _ hat _ _ => hheap a hat⟩
  intro c' fst' h'
  rw [ht0] at h'
  simp only [Option.some.injEq, Obj.plain.injEq] at h'
  obtain ⟨rfl, -⟩ := h'
  exact ⟨f1, ht1⟩

/-- The scratch array after `readAll(inoutTemp, 0, k)` keeps its length. -/
theorem slow_len {src : Bytes} {w : List Value} {k : Nat} (hk : (BitVec.ofNat 32 k : I32).toNat ≤ src.length)
    (hw : w.length = 16) (hk16 : k ≤ 16) :
    (List.take (0#32 : I32).toNat w ++ (List.take (BitVec.ofNat 32 k : I32).toNat (List.map jbyte src) ++
      List.drop k w)).length = 16 := by
  have e : (BitVec.ofNat 32 k : I32).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  rw [e] at hk ⊢
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop, hw,
    show (0#32 : I32).toNat = 0 from rfl]
  omega

/-! ## `readI16()` -/

abbrev ri16Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«readI16()».ref

/-- What `readI16()` guarantees: the next two bytes, big-endian, as a `short`. -/
def ri16N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    ∃ u0 u1 rest x, R.src σ t = u0 :: u1 :: rest ∧ r = some (.int x) ∧
      x.toInt = Spec.toS 16 (256 * u0.toNat + u1.toNat) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp

/-- `readI16()` on fewer than two bytes: a `TTransportException`. -/
def ri16E (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    (R.src σ t).length < 2 ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] ri16N ri16E

def ri16Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp)
  (ri16N P R) (ri16E P R)

def ri16SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp ∧ BPAtH P R σ p t tmp ∧
     ClassOK P σ t)
  (ri16N P R) (ri16E P R)

/-- Statement 15 (`label2`): the two bytes at `buf[off]` are the source's next two bytes. -/
def ri16Inv (R : TRep) : Invariants := [(15, fun args σ0 fr σ =>
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
  Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (bufA : Addr) (arr : List Value) (off : Nat) (u0 u1 : UInt8),
    fr.get 2 = some (.ref p) ∧ fr.get 1 = some (.ref bufA) ∧ fr.get 7 = some (.int (BitVec.ofNat 32 off)) ∧
    σ.heap bufA = some (.array (.prim .byte) arr) ∧ off + 2 ≤ arr.length ∧ off + 2 < 2147483648 ∧
    arr[off]? = some (jbyte u0) ∧ arr[off + 1]? = some (jbyte u1) ∧
    R.src σ0 t = u0 :: u1 :: R.src σ t ∧ RdFrame R σ0 σ p t tmp)]

theorem ri16_exc_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hBP : BPAtH P R σ p t tmp)
    (hlen : (R.src σ t).length < (2#32 : I32).toNat) (he : σ'.heap e = some (.plain ttExcCls w)) :
    ri16E P R [.ref p] σ e σ' := by
  have hC := BPAtH.elim hBP
  unfold ri16E
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hC
  exact ⟨by simpa using hlen, w, he⟩

/-- `readAll` filled `inoutTemp[0..2)`: the cut point's facts. -/
theorem ri16_slow_cut {src : Bytes} {w : List Value} {F : Prop} (hlen2 : (2#32 : I32).toNat ≤ src.length)
    (hF : F) :
    ∃ x, 0#32 = BitVec.ofNat 32 x ∧
      x + 2 ≤ (Option.map jbyte src[0]?).toList.length + ((Option.map jbyte src[1]?).toList.length + 14) ∧
      x + 2 < 2147483648 ∧
      ∃ x_1, ((Option.map jbyte src[0]?).toList ++ ((Option.map jbyte src[1]?).toList ++ List.drop 2 w))[x]? =
          some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
      ∃ x_2, ((Option.map jbyte src[0]?).toList ++ ((Option.map jbyte src[1]?).toList ++ List.drop 2 w))[x + 1]? =
          some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      src = x_1 :: x_2 :: List.drop 2 src ∧ F := by
  obtain ⟨u0, u1, rest, rfl⟩ : ∃ u0 u1 rest, src = u0 :: u1 :: rest := by
    match src, hlen2 with
    | u0 :: u1 :: rest, _ => exact ⟨u0, u1, rest, rfl⟩
    | [], h => simp at h
    | [_], h => simp at h
  exact ⟨0, rfl, Nat.le_of_ble_eq_true rfl, by decide, u0, rfl, u1, rfl, rfl, hF⟩

/-- The buffer fast path: the cut point's facts. -/
theorem ri16_fast_cut {R : TRep} {σ0 : State} {t : Addr} {arr : List Value} {u : UInt8} {rest : Bytes}
    {F : Prop} (hge : ¬ R.bufLen σ0 t < 2)
    (hpl : R.bufPos σ0 t + (R.bufLen σ0 t).toNat ≤ arr.length)
    (heqb : List.take (R.bufLen σ0 t).toNat (List.drop (R.bufPos σ0 t) arr) =
      List.take (R.bufLen σ0 t).toNat (List.map jbyte (R.src σ0 t)))
    (hle : R.bufLen σ0 t ≤ ((R.src σ0 t).length : Int))
    (hlt : R.bufPos σ0 t + (R.bufLen σ0 t).toNat < 2147483648)
    (hsrc0 : R.src σ0 t = u :: rest) (hF : F) :
    ∃ x x_1, BitVec.ofNat 32 (R.bufPos σ0 t) = BitVec.ofNat 32 x_1 ∧ arr = x ∧ x_1 + 2 ≤ x.length ∧
      x_1 + 2 < 2147483648 ∧
      ∃ x_2, x[x_1]? = some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      ∃ x_3, x[x_1 + 1]? = some (Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      (u = x_2 ∧ rest = x_3 :: rest.tail) ∧ F := by
  rw [hsrc0] at heqb hle
  obtain ⟨u1, rest', rfl⟩ : ∃ u1 rest', rest = u1 :: rest' := by
    match rest, hle with
    | u1 :: rest', _ => exact ⟨u1, rest', rfl⟩
    | [], h => simp at h; omega
  have hL : 2 ≤ (R.bufLen σ0 t).toNat := by omega
  have ek : ∀ k, k < 2 → arr[R.bufPos σ0 t + k]? = ((u :: u1 :: rest')[k]?).map jbyte := by
    intro k hk
    have := congrArg (fun l => l[k]?) heqb
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, List.getElem?_take_of_lt (by omega),
      List.getElem?_map] at this
    exact this
  refine ⟨arr, R.bufPos σ0 t, rfl, rfl, by omega, by omega, u, ?_, u1, ?_, ⟨rfl, rfl⟩, hF⟩
  · have e0 := ek 0 (by decide)
    rw [Nat.add_zero] at e0
    rw [e0]
    rfl
  · rw [ek 1 (by decide)]
    rfl

/-- The return: the value of the two bytes, as a `short`. -/
theorem ri16_ret_post {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {arr : List Value}
    {off : Nat} {u0 u1 : UInt8} {v1 v0 : I32} {xs : List Value} {c : ClassName}
    {f0 f1 : List (FieldKey × Value)}
    (hBP : BPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = u0 :: u1 :: R.src σ t)
    (h0 : arr[off]? = some (Value.int (BitVec.signExtend 32 u0.toBitVec)))
    (h1 : arr[off + 1]? = some (Value.int (BitVec.signExtend 32 u1.toBitVec)))
    (hinv : R.inv σ t) (hsink : R.sink σ t = R.sink σ0 t) (hnext : σ0.next ≤ σ.next)
    (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics) (hp : σ.heap p = σ0.heap p)
    (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hxs : xs.length = 16)
    (hop : ¬R.owns σ t p) (hot : ¬R.owns σ t tmp)
    (hfr : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a)
    (ht0 : σ0.heap t = some (.plain c f0)) (ht1 : σ.heap t = some (.plain c f1))
    {hb1 : off < arr.length} (hd1 : arr[off]'hb1 = Value.int v1)
    {hb0 : off + 1 < arr.length} (hd0 : arr[off + 1]'hb0 = Value.int v0) :
    ri16N P R [.ref p] σ0
      (some (.int (JInt.toShort (JInt.shl (JInt.toShort v1 &&& 255#32) 8#32 ||| JInt.toShort v0 &&& 255#32))))
      σ := by
  have ev1 : v1 = BitVec.signExtend 32 u0.toBitVec := by
    rw [List.getElem?_eq_getElem hb1, hd1] at h0
    simpa using h0
  have ev0 : v0 = BitVec.signExtend 32 u1.toBitVec := by
    rw [List.getElem?_eq_getElem hb0, hd0] at h1
    simpa using h1
  subst ev1 ev0
  obtain ⟨fs, xs0, c0, fst, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop0, hot0⟩ :=
    BPAtH.elim hBP
  rw [hth] at ht0
  simp only [Option.some.injEq, Obj.plain.injEq] at ht0
  obtain ⟨rfl, -⟩ := ht0
  unfold ri16N
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' (BPAtH.elim hBP)
  refine ⟨u0, u1, R.src σ t, _, hsrc, rfl, ri16_val u0 u1, rfl, hsink, ?_, ⟨hnext, hin, hst, hfr⟩⟩
  exact ⟨fs, xs, c0, f1, by rw [hp]; exact hph, htr, hte, htmp, hxs, ht1, hc1, hc2, hinv, hpt, htt, hptm,
    hop, hot⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri16_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 1
    ri16Ref (fun P => ri16SpecI P R) (ri16Inv R) 60 := by
  jverify_body [Contains, BPAt, ClassOK, ri16SpecI, ri16Inv, tc_write, tc_readAll,
    tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls]
  case left.some.true.normal.isTrue.left => exact br_readAll_pre R ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case left.some.true.normal.isTrue.right.normal =>
    exact ri16_slow_cut ‹_› (rdFrame_slow ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (slow_len ‹_› ‹_› (by decide)) ‹_›
      ‹_› ‹_› ‹_›)
  case left.some.true.normal.isTrue.right.exc => exact ri16_exc_post ‹_› ‹_› ‹_›
  case left.some.true.normal.isFalse.right.normal.right.normal.right.normal =>
    exact ri16_fast_cut ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (rdFrame_fast ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case right.isTrue.int.isTrue.int =>
    exact ri16_ret_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

theorem ri16_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P ri16Ref (ri16Spec P R) := by
  have hI := BodyVCP.sat (ri16_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩ hm

theorem readI16_cons (u0 u1 : UInt8) (rest : Spec.Bytes) :
    Spec.readI16 (u0 :: u1 :: rest) = some (Spec.toS 16 (256 * u0.toNat + u1.toNat), rest) := by
  simp [Spec.readI16, Spec.readBE, Spec.beVal, Spec.Truncated]

theorem ofInt_of_toInt {x : I32} {v : Int} (h : x.toInt = v) (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    x = BitVec.ofInt 32 v := by
  apply BitVec.eq_of_toInt_eq
  rw [h, BitVec.toInt_ofInt]
  exact (bmod32_of_bounds h1 (by omega)).symm

/-- **D for binary i16**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `readI16()` on a source `Spec.beI16 v ++ rest` (any `i16`
value `v`) returns `v` and leaves `rest`. -/
theorem ri16_D {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (v : Int) (hv : Spec.InI16 v) (rest : Spec.Bytes) (hsrc : R.src σ t = Spec.beI16 v ++ rest)
    {o : Outcome} (hm : MExec P ri16Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.int (BitVec.ofInt 32 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := ri16_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri16Spec, Spec.of] at hpost
    unfold ri16N at hpost
    obtain ⟨u0, u1, rest', x, hs, hr, hx, hs', hsink, hBP', -⟩ := hpost p t tmp rfl hBP
    have h1 := Spec.readI16_beI16 hv rest
    rw [← hsrc, hs, readI16_cons] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv', hr'⟩ := h1
    unfold Spec.InI16 at hv
    refine ⟨σ', by rw [hr, ofInt_of_toInt (hx.trans hv') (by omega) (by omega)], by rw [hs', hr'], hsink, hBP'⟩
  | exc e σ' =>
    simp only [ri16Spec, Spec.of] at hpost
    unfold ri16E at hpost
    obtain ⟨hlen, -⟩ := hpost p t tmp rfl hBP
    rw [hsrc, List.length_append, Spec.beI16, Spec.be_length] at hlen
    omega
  | wrong msg => simp only [ri16Spec, Spec.of] at hpost

/-- **M for binary i16**: on fewer than two bytes, `readI16()` throws a `TTransportException` (the
transport's, from `readAll`); `Spec.readI16` is `none` exactly there. -/
theorem ri16_M {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (hshort : (R.src σ t).length < 2) {o : Outcome} (hm : MExec P ri16Ref [.ref p] σ o) :
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) := by
  have hpost := ri16_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri16Spec, Spec.of] at hpost
    unfold ri16N at hpost
    obtain ⟨u0, u1, rest', x, hs, -⟩ := hpost p t tmp rfl hBP
    rw [hs] at hshort
    simp only [List.length_cons] at hshort
    omega
  | exc e σ' =>
    simp only [ri16Spec, Spec.of] at hpost
    unfold ri16E at hpost
    obtain ⟨-, hexc⟩ := hpost p t tmp rfl hBP
    exact ⟨e, σ', rfl, hexc⟩
  | wrong msg => simp only [ri16Spec, Spec.of] at hpost

/-! ## `readI32()` -/

abbrev ri32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«readI32()».ref

/-- What `readI32()` guarantees: the next four bytes, big-endian, as an `int`. -/
def ri32N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    ∃ u0 u1 u2 u3 rest x, R.src σ t = u0 :: u1 :: u2 :: u3 :: rest ∧ r = some (.int x) ∧
      x.toInt = Spec.toS 32 (2 ^ 24 * u0.toNat + 2 ^ 16 * u1.toNat + 2 ^ 8 * u2.toNat + u3.toNat) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp

/-- `readI32()` on fewer than four bytes: a `TTransportException`. -/
def ri32E (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    (R.src σ t).length < 4 ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] ri32N ri32E

def ri32Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp)
  (ri32N P R) (ri32E P R)

def ri32SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp ∧ BPAtH P R σ p t tmp ∧
     ClassOK P σ t)
  (ri32N P R) (ri32E P R)

/-- Statement 15 (`label2`): the four bytes at `buf[off]` are the source's next four bytes. -/
def ri32Inv (R : TRep) : Invariants := [(15, fun args σ0 fr σ =>
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
  Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (bufA : Addr) (arr : List Value) (off : Nat) (u0 u1 u2 u3 : UInt8),
    fr.get 2 = some (.ref p) ∧ fr.get 1 = some (.ref bufA) ∧ fr.get 8 = some (.int (BitVec.ofNat 32 off)) ∧
    σ.heap bufA = some (.array (.prim .byte) arr) ∧ off + 4 ≤ arr.length ∧ off + 4 < 2147483648 ∧
    arr[off]? = some (jbyte u0) ∧ arr[off + 1]? = some (jbyte u1) ∧ arr[off + 2]? = some (jbyte u2) ∧
    arr[off + 3]? = some (jbyte u3) ∧
    (∃ h : off < arr.length, arr[off]'h = jbyte u0) ∧ (∃ h : off + 1 < arr.length, arr[off + 1]'h = jbyte u1) ∧
    (∃ h : off + 2 < arr.length, arr[off + 2]'h = jbyte u2) ∧ (∃ h : off + 3 < arr.length, arr[off + 3]'h = jbyte u3) ∧
    R.src σ0 t = u0 :: u1 :: u2 :: u3 :: R.src σ t ∧ RdFrame R σ0 σ p t tmp)]

/-- Two values whose bits do not overlap (`a` a multiple of `2 ^ s`, `b < 2 ^ s`): `|` adds them. -/
theorem or_ofNat' (w a b s : Nat) (ha : a % 2 ^ s = 0) (hb : b < 2 ^ s) (h : a + b < 2 ^ w) :
    BitVec.ofNat w a ||| BitVec.ofNat w b = BitVec.ofNat w (a + b) := by
  obtain ⟨c, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ s * c < 2 ^ w), Nat.mod_eq_of_lt (by omega : b < 2 ^ w),
    Nat.mod_eq_of_lt h, ← Nat.two_pow_add_eq_or_of_lt hb]

/-- The value `readI32()` computes from the four bytes. -/
theorem ri32_val (u0 u1 u2 u3 : UInt8) :
    (JInt.shl (JInt.toShort (BitVec.signExtend 32 u0.toBitVec) &&& 255#32) 24#32 |||
          JInt.shl (JInt.toShort (BitVec.signExtend 32 u1.toBitVec) &&& 255#32) 16#32 |||
        JInt.shl (JInt.toShort (BitVec.signExtend 32 u2.toBitVec) &&& 255#32) 8#32 |||
      JInt.toShort (BitVec.signExtend 32 u3.toBitVec) &&& 255#32).toInt =
      Spec.toS 32 (2 ^ 24 * u0.toNat + 2 ^ 16 * u1.toNat + 2 ^ 8 * u2.toNat + u3.toNat) := by
  have h0 := u0.toNat_lt
  have h1 := u1.toNat_lt
  have h2 := u2.toNat_lt
  have h3 := u3.toNat_lt
  rw [byte_and255, byte_and255, byte_and255, byte_and255,
    shl_ofNat32 u0.toNat 24 (by decide) (by omega), shl_ofNat32 u1.toNat 16 (by decide) (by omega),
    shl_ofNat32 u2.toNat 8 (by decide) (by omega),
    or_ofNat' 32 _ _ 24 (by omega) (by omega) (by omega), or_ofNat' 32 _ _ 16 (by omega) (by omega) (by omega),
    or_ofNat' 32 _ _ 8 (by omega) (by omega) (by omega), BitVec.toInt_ofNat']
  show _ = Int.bmod _ _
  congr 1
  omega

theorem ri32_exc_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hBP : BPAtH P R σ p t tmp)
    (hlen : (R.src σ t).length < (4#32 : I32).toNat) (he : σ'.heap e = some (.plain ttExcCls w)) :
    ri32E P R [.ref p] σ e σ' := by
  have hC := BPAtH.elim hBP
  unfold ri32E
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hC
  exact ⟨by simpa using hlen, w, he⟩

/-- `inoutTemp` after `readAll(inoutTemp, 0, 4)` on the source `src` (old contents `w`). -/
abbrev rd4Arr (src : Bytes) (w : List Value) : List Value :=
  (Option.map jbyte src[0]?).toList ++ ((Option.map jbyte src[1]?).toList ++
    ((Option.map jbyte src[2]?).toList ++ ((Option.map jbyte src[3]?).toList ++ List.drop 4 w)))

/-- Its length, in the form the VC states it. -/
abbrev rd4Len (src : Bytes) : Nat :=
  (Option.map jbyte src[0]?).toList.length + ((Option.map jbyte src[1]?).toList.length +
    ((Option.map jbyte src[2]?).toList.length + ((Option.map jbyte src[3]?).toList.length + 12)))

theorem rd4_lt {src : Bytes} {w : List Value} {i : Nat} (hw : w.length = 16) (h : i < rd4Len src) :
    i < (rd4Arr src w).length := by
  simp only [rd4Arr, rd4Len, List.length_append, List.length_drop, hw] at h ⊢
  omega

/-- `readAll` filled `inoutTemp[0..4)`: the cut point's facts. -/
theorem ri32_slow_cut {src : Bytes} {w : List Value} {F : Prop} (hlen : (4#32 : I32).toNat ≤ src.length)
    (hw : w.length = 16) (hF : F) :
    ∃ x, 0#32 = BitVec.ofNat 32 x ∧ x + 4 ≤ rd4Len src ∧ x + 4 < 2147483648 ∧
      ∃ x_1, (rd4Arr src w)[x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
      ∃ x_2, (rd4Arr src w)[x + 1]? = some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      ∃ x_3, (rd4Arr src w)[x + 2]? = some (Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      ∃ x_4, (rd4Arr src w)[x + 3]? = some (Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      (∃ h : x < rd4Len src,
        (rd4Arr src w)[x]'(rd4_lt hw h) = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
      (∃ h : x + 1 < rd4Len src,
        (rd4Arr src w)[x + 1]'(rd4_lt hw h) = Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      (∃ h : x + 2 < rd4Len src,
        (rd4Arr src w)[x + 2]'(rd4_lt hw h) = Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      (∃ h : x + 3 < rd4Len src,
        (rd4Arr src w)[x + 3]'(rd4_lt hw h) = Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      src = x_1 :: x_2 :: x_3 :: x_4 :: List.drop 4 src ∧ F := by
  obtain ⟨u0, u1, u2, u3, rest, rfl⟩ : ∃ u0 u1 u2 u3 rest, src = u0 :: u1 :: u2 :: u3 :: rest := by
    match src, hlen with
    | u0 :: u1 :: u2 :: u3 :: rest, _ => exact ⟨u0, u1, u2, u3, rest, rfl⟩
    | [], h => simp at h
    | [_], h => simp at h
    | [_, _], h => simp at h
    | [_, _, _], h => simp at h
  have hk : ∀ k, k < 4 → k < rd4Len (u0 :: u1 :: u2 :: u3 :: rest) := fun k hk => by
    show k < 1 + (1 + (1 + (1 + 12)))
    omega
  exact ⟨0, rfl, Nat.le_of_ble_eq_true rfl, by decide, u0, rfl, u1, rfl, u2, rfl, u3, rfl,
    ⟨hk 0 (by decide), rfl⟩, ⟨hk 1 (by decide), rfl⟩,
    ⟨hk 2 (by decide), rfl⟩, ⟨hk 3 (by decide), rfl⟩, rfl, hF⟩


/-- The buffer fast path: the cut point's facts. -/
theorem ri32_fast_cut {R : TRep} {σ0 : State} {t : Addr} {arr : List Value} {u : UInt8} {rest : Bytes}
    {F : Prop} (hge : ¬ R.bufLen σ0 t < 4)
    (hpl : R.bufPos σ0 t + (R.bufLen σ0 t).toNat ≤ arr.length)
    (heqb : List.take (R.bufLen σ0 t).toNat (List.drop (R.bufPos σ0 t) arr) =
      List.take (R.bufLen σ0 t).toNat (List.map jbyte (R.src σ0 t)))
    (hle : R.bufLen σ0 t ≤ ((R.src σ0 t).length : Int))
    (hlt : R.bufPos σ0 t + (R.bufLen σ0 t).toNat < 2147483648)
    (hsrc0 : R.src σ0 t = u :: rest) (hF : F) :
    ∃ x x_1, BitVec.ofNat 32 (R.bufPos σ0 t) = BitVec.ofNat 32 x_1 ∧ arr = x ∧ x_1 + 4 ≤ x.length ∧
      x_1 + 4 < 2147483648 ∧
      ∃ x_2, x[x_1]? = some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      ∃ x_3, x[x_1 + 1]? = some (Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      ∃ x_4, x[x_1 + 2]? = some (Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      ∃ x_5, x[x_1 + 3]? = some (Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      (∃ h : x_1 < x.length, x[x_1]'h = Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      (∃ h : x_1 + 1 < x.length, x[x_1 + 1]'h = Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      (∃ h : x_1 + 2 < x.length, x[x_1 + 2]'h = Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      (∃ h : x_1 + 3 < x.length, x[x_1 + 3]'h = Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      (u = x_2 ∧ rest = x_3 :: x_4 :: x_5 :: List.drop 3 rest) ∧ F := by
  rw [hsrc0] at heqb hle
  obtain ⟨v1, v2, v3, rest', rfl⟩ : ∃ v1 v2 v3 rest', rest = v1 :: v2 :: v3 :: rest' := by
    match rest, hle with
    | v1 :: v2 :: v3 :: rest', _ => exact ⟨v1, v2, v3, rest', rfl⟩
    | [], h => simp at h; omega
    | [_], h => simp at h; omega
    | [_, _], h => simp at h; omega
  have hL : 4 ≤ (R.bufLen σ0 t).toNat := by omega
  have ek : ∀ k, k < 4 → arr[R.bufPos σ0 t + k]? = ((u :: v1 :: v2 :: v3 :: rest')[k]?).map jbyte := by
    intro k hk
    have := congrArg (fun l => l[k]?) heqb
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, List.getElem?_take_of_lt (by omega),
      List.getElem?_map] at this
    exact this
  have e0 : arr[R.bufPos σ0 t]? = some (Value.int (BitVec.signExtend 32 u.toBitVec)) := by
    have := ek 0 (by decide)
    rw [Nat.add_zero] at this
    rw [this]
    rfl
  have e1 : arr[R.bufPos σ0 t + 1]? = some (Value.int (BitVec.signExtend 32 v1.toBitVec)) := by
    rw [ek 1 (by decide)]
    rfl
  have e2 : arr[R.bufPos σ0 t + 2]? = some (Value.int (BitVec.signExtend 32 v2.toBitVec)) := by
    rw [ek 2 (by decide)]
    rfl
  have e3 : arr[R.bufPos σ0 t + 3]? = some (Value.int (BitVec.signExtend 32 v3.toBitVec)) := by
    rw [ek 3 (by decide)]
    rfl
  exact ⟨arr, R.bufPos σ0 t, rfl, rfl, by omega, by omega, u, e0, v1, e1, v2, e2, v3, e3,
    List.getElem?_eq_some_iff.mp e0, List.getElem?_eq_some_iff.mp e1,
    List.getElem?_eq_some_iff.mp e2, List.getElem?_eq_some_iff.mp e3, ⟨rfl, rfl⟩, hF⟩

/-- The return: the value of the four bytes. -/
theorem ri32_ret_post {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {u0 u1 u2 u3 : UInt8}
    {xs : List Value} {c : ClassName} {f0 f1 : List (FieldKey × Value)}
    (hBP : BPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = u0 :: u1 :: u2 :: u3 :: R.src σ t)
    (hinv : R.inv σ t) (hsink : R.sink σ t = R.sink σ0 t) (hnext : σ0.next ≤ σ.next)
    (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics) (hp : σ.heap p = σ0.heap p)
    (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hxs : xs.length = 16)
    (hop : ¬R.owns σ t p) (hot : ¬R.owns σ t tmp)
    (hfr : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a)
    (ht0 : σ0.heap t = some (.plain c f0)) (ht1 : σ.heap t = some (.plain c f1)) :
    ri32N P R [.ref p] σ0
      (some (.int (JInt.shl (JInt.toShort (BitVec.signExtend 32 u0.toBitVec) &&& 255#32) 24#32 |||
          JInt.shl (JInt.toShort (BitVec.signExtend 32 u1.toBitVec) &&& 255#32) 16#32 |||
        JInt.shl (JInt.toShort (BitVec.signExtend 32 u2.toBitVec) &&& 255#32) 8#32 |||
      JInt.toShort (BitVec.signExtend 32 u3.toBitVec) &&& 255#32))) σ := by
  obtain ⟨fs, xs0, c0, fst, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop0, hot0⟩ :=
    BPAtH.elim hBP
  rw [hth] at ht0
  simp only [Option.some.injEq, Obj.plain.injEq] at ht0
  obtain ⟨rfl, -⟩ := ht0
  unfold ri32N
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' (BPAtH.elim hBP)
  refine ⟨u0, u1, u2, u3, R.src σ t, _, hsrc, rfl, ri32_val u0 u1 u2 u3, rfl, hsink, ?_, ⟨hnext, hin, hst, hfr⟩⟩
  exact ⟨fs, xs, c0, f1, by rw [hp]; exact hph, htr, hte, htmp, hxs, ht1, hc1, hc2, hinv, hpt, htt, hptm,
    hop, hot⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri32_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 1
    ri32Ref (fun P => ri32SpecI P R) (ri32Inv R) 60 := by
  jverify_body [Contains, BPAt, ClassOK, ri32SpecI, ri32Inv, tc_write, tc_readAll,
    tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls]
  case left.some.true.normal.isTrue.left => exact br_readAll_pre R ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case left.some.true.normal.isTrue.right.normal =>
    exact ri32_slow_cut ‹_› ‹_› (rdFrame_slow ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (slow_len ‹_› ‹_› (by decide)) ‹_›
      ‹_› ‹_› ‹_›)
  case left.some.true.normal.isTrue.right.exc => exact ri32_exc_post ‹_› ‹_› ‹_›
  case left.some.true.normal.isFalse.right.normal.right.normal.right.normal =>
    exact ri32_fast_cut ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (rdFrame_fast ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case right.isTrue.isTrue.isTrue =>
    exact ri32_ret_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

theorem ri32_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P ri32Ref (ri32Spec P R) := by
  have hI := BodyVCP.sat (ri32_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩ hm

theorem readI32_cons (u0 u1 u2 u3 : UInt8) (rest : Spec.Bytes) :
    Spec.readI32 (u0 :: u1 :: u2 :: u3 :: rest) =
      some (Spec.toS 32 (2 ^ 24 * u0.toNat + 2 ^ 16 * u1.toNat + 2 ^ 8 * u2.toNat + u3.toNat), rest) := by
  simp only [Spec.readI32, Spec.readBE, Spec.beVal, Spec.Truncated]
  simp only [List.length_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.foldl_cons, List.foldl_nil]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  omega

/-- **D for binary i32**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `readI32()` on a source `Spec.beI32 v ++ rest` (any `i32`
value `v`) returns `v` and leaves `rest`. -/
theorem ri32_D {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (v : Int) (hv : Spec.InI32 v) (rest : Spec.Bytes) (hsrc : R.src σ t = Spec.beI32 v ++ rest)
    {o : Outcome} (hm : MExec P ri32Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.int (BitVec.ofInt 32 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := ri32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri32Spec, Spec.of] at hpost
    unfold ri32N at hpost
    obtain ⟨u0, u1, u2, u3, rest', x, hs, hr, hx, hs', hsink, hBP', -⟩ := hpost p t tmp rfl hBP
    have h1 := Spec.readI32_beI32 hv rest
    rw [← hsrc, hs, readI32_cons] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv', hr'⟩ := h1
    unfold Spec.InI32 at hv
    refine ⟨σ', by rw [hr, ofInt_of_toInt (hx.trans hv') (by omega) (by omega)], by rw [hs', hr'], hsink, hBP'⟩
  | exc e σ' =>
    simp only [ri32Spec, Spec.of] at hpost
    unfold ri32E at hpost
    obtain ⟨hlen, -⟩ := hpost p t tmp rfl hBP
    rw [hsrc, List.length_append, Spec.beI32, Spec.be_length] at hlen
    omega
  | wrong msg => simp only [ri32Spec, Spec.of] at hpost

/-- **M for binary i32**: on fewer than four bytes, `readI32()` throws a `TTransportException` (the
transport's, from `readAll`); `Spec.readI32` is `none` exactly there. -/
theorem ri32_M {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (hshort : (R.src σ t).length < 4) {o : Outcome} (hm : MExec P ri32Ref [.ref p] σ o) :
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) := by
  have hpost := ri32_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri32Spec, Spec.of] at hpost
    unfold ri32N at hpost
    obtain ⟨u0, u1, u2, u3, rest', x, hs, -⟩ := hpost p t tmp rfl hBP
    rw [hs] at hshort
    simp only [List.length_cons] at hshort
    omega
  | exc e σ' =>
    simp only [ri32Spec, Spec.of] at hpost
    unfold ri32E at hpost
    obtain ⟨-, hexc⟩ := hpost p t tmp rfl hBP
    exact ⟨e, σ', rfl, hexc⟩
  | wrong msg => simp only [ri32Spec, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
