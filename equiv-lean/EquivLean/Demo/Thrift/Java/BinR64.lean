import EquivLean.Demo.Thrift.Java.BinR

/-!
# Thrift → Java (T4): `TBinaryProtocol.readI64` reads the eight big-endian bytes (D, M)

The proof of `readI32()` (`BinR`) with eight bytes: one cut point, at `label2` (statement 15), where
the eight bytes at `buf[off …]` are the source's next eight bytes; the value is combined in `long`s.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## Bytes to a `long` -/

/-- A byte read from the wire, `& 0xFF`, widened to `long`: its unsigned value. -/
theorem toLong_byte (u : UInt8) :
    JInt.toLong (JInt.toShort (BitVec.signExtend 32 u.toBitVec) &&& 255#32) = BitVec.ofNat 64 u.toNat := by
  have hu := u.toNat_lt
  have hm : (BitVec.ofNat 32 u.toNat).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show u.toNat < 2 ^ 32 by omega)]
    exact decide_eq_false (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [byte_and255, JInt.toLong, BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem shl_ofNat64 (a s : Nat) (hs : s < 64) (h : a * 2 ^ s < 2 ^ 64) :
    JLong.shl (BitVec.ofNat 64 a) (BitVec.ofNat 32 s) = BitVec.ofNat 64 (a * 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp only [JLong.shl, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have ha : a < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right a (Nat.two_pow_pos s)) h
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ha,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- The value `readI64()` computes from the eight bytes. -/
theorem ri64_val (u0 u1 u2 u3 u4 u5 u6 u7 : UInt8) :
    (JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u0.toBitVec) &&& 255#32)) 56#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u1.toBitVec) &&& 255#32)) 48#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u2.toBitVec) &&& 255#32)) 40#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u3.toBitVec) &&& 255#32)) 32#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u4.toBitVec) &&& 255#32)) 24#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u5.toBitVec) &&& 255#32)) 16#32 |||
      JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u6.toBitVec) &&& 255#32)) 8#32 |||
      JInt.toLong (JInt.toShort (BitVec.signExtend 32 u7.toBitVec) &&& 255#32)).toInt =
      Spec.toS 64 (2 ^ 56 * u0.toNat + 2 ^ 48 * u1.toNat + 2 ^ 40 * u2.toNat + 2 ^ 32 * u3.toNat +
        2 ^ 24 * u4.toNat + 2 ^ 16 * u5.toNat + 2 ^ 8 * u6.toNat + u7.toNat) := by
  have h0 := u0.toNat_lt
  have h1 := u1.toNat_lt
  have h2 := u2.toNat_lt
  have h3 := u3.toNat_lt
  have h4 := u4.toNat_lt
  have h5 := u5.toNat_lt
  have h6 := u6.toNat_lt
  have h7 := u7.toNat_lt
  simp only [toLong_byte]
  rw [shl_ofNat64 u0.toNat 56 (by decide) (by omega),
    shl_ofNat64 u1.toNat 48 (by decide) (by omega),
    shl_ofNat64 u2.toNat 40 (by decide) (by omega),
    shl_ofNat64 u3.toNat 32 (by decide) (by omega),
    shl_ofNat64 u4.toNat 24 (by decide) (by omega),
    shl_ofNat64 u5.toNat 16 (by decide) (by omega),
    shl_ofNat64 u6.toNat 8 (by decide) (by omega),
    or_ofNat' 64 _ _ 56 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 48 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 40 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 32 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 24 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 16 (by omega) (by omega) (by omega),
    or_ofNat' 64 _ _ 8 (by omega) (by omega) (by omega),
    BitVec.toInt_ofNat']
  show _ = Int.bmod _ _
  congr 1
  omega

/-! ## `readI64()` -/

abbrev ri64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«readI64()».ref

/-- What `readI64()` guarantees: the next eight bytes, big-endian, as a `long`. -/
def ri64N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    ∃ u0 u1 u2 u3 u4 u5 u6 u7 rest x, R.src σ t = u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: rest ∧
      r = some (.long x) ∧
      x.toInt = Spec.toS 64 (2 ^ 56 * u0.toNat + 2 ^ 48 * u1.toNat + 2 ^ 40 * u2.toNat + 2 ^ 32 * u3.toNat +
        2 ^ 24 * u4.toNat + 2 ^ 16 * u5.toNat + 2 ^ 8 * u6.toNat + u7.toNat) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp

/-- `readI64()` on fewer than eight bytes: a `TTransportException`. -/
def ri64E (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → BPAt P R σ p t tmp →
    (R.src σ t).length < 8 ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] ri64N ri64E

def ri64Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp)
  (ri64N P R) (ri64E P R)

def ri64SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ BPAt P R σ p t tmp ∧ BPAtH P R σ p t tmp ∧
     ClassOK P σ t)
  (ri64N P R) (ri64E P R)

/-- Statement 15 (`label2`): the eight bytes at `buf[off]` are the source's next eight bytes. -/
def ri64Inv (R : TRep) : Invariants := [(15, fun args σ0 fr σ =>
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
  Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (bufA : Addr) (arr : List Value) (off : Nat) (u0 u1 u2 u3 u4 u5 u6 u7 : UInt8),
    fr.get 4 = some (.ref p) ∧ fr.get 1 = some (.ref bufA) ∧ fr.get 9 = some (.int (BitVec.ofNat 32 off)) ∧
    σ.heap bufA = some (.array (.prim .byte) arr) ∧ off + 8 ≤ arr.length ∧ off + 8 < 2147483648 ∧
    arr[off]? = some (jbyte u0) ∧ arr[off + 1]? = some (jbyte u1) ∧
    arr[off + 2]? = some (jbyte u2) ∧ arr[off + 3]? = some (jbyte u3) ∧
    arr[off + 4]? = some (jbyte u4) ∧ arr[off + 5]? = some (jbyte u5) ∧
    arr[off + 6]? = some (jbyte u6) ∧ arr[off + 7]? = some (jbyte u7) ∧
    (∃ h : off < arr.length, arr[off]'h = jbyte u0) ∧
    (∃ h : off + 1 < arr.length, arr[off + 1]'h = jbyte u1) ∧
    (∃ h : off + 2 < arr.length, arr[off + 2]'h = jbyte u2) ∧
    (∃ h : off + 3 < arr.length, arr[off + 3]'h = jbyte u3) ∧
    (∃ h : off + 4 < arr.length, arr[off + 4]'h = jbyte u4) ∧
    (∃ h : off + 5 < arr.length, arr[off + 5]'h = jbyte u5) ∧
    (∃ h : off + 6 < arr.length, arr[off + 6]'h = jbyte u6) ∧
    (∃ h : off + 7 < arr.length, arr[off + 7]'h = jbyte u7) ∧
    R.src σ0 t = u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: R.src σ t ∧ RdFrame R σ0 σ p t tmp)]

theorem ri64_exc_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hBP : BPAtH P R σ p t tmp)
    (hlen : (R.src σ t).length < (8#32 : I32).toNat) (he : σ'.heap e = some (.plain ttExcCls w)) :
    ri64E P R [.ref p] σ e σ' := by
  have hC := BPAtH.elim hBP
  unfold ri64E
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hC
  exact ⟨by simpa using hlen, w, he⟩

/-- `inoutTemp` after `readAll(inoutTemp, 0, 8)` on the source `src` (old contents `w`). -/
abbrev rd8Arr (src : Bytes) (w : List Value) : List Value :=
  (Option.map jbyte src[0]?).toList ++ ((Option.map jbyte src[1]?).toList ++
    ((Option.map jbyte src[2]?).toList ++ ((Option.map jbyte src[3]?).toList ++
    ((Option.map jbyte src[4]?).toList ++ ((Option.map jbyte src[5]?).toList ++
    ((Option.map jbyte src[6]?).toList ++ ((Option.map jbyte src[7]?).toList ++ List.drop 8 w)))))))

/-- Its length, in the form the VC states it. -/
abbrev rd8Len (src : Bytes) : Nat :=
  (Option.map jbyte src[0]?).toList.length + ((Option.map jbyte src[1]?).toList.length +
    ((Option.map jbyte src[2]?).toList.length + ((Option.map jbyte src[3]?).toList.length +
    ((Option.map jbyte src[4]?).toList.length + ((Option.map jbyte src[5]?).toList.length +
    ((Option.map jbyte src[6]?).toList.length + ((Option.map jbyte src[7]?).toList.length + 8)))))))

theorem rd8_lt {src : Bytes} {w : List Value} {i : Nat} (hw : w.length = 16) (h : i < rd8Len src) :
    i < (rd8Arr src w).length := by
  simp only [rd8Arr, rd8Len, List.length_append, List.length_drop, hw] at h ⊢
  omega

/-- `readAll` filled `inoutTemp[0..8)`: the cut point's facts. -/
theorem ri64_slow_cut {src : Bytes} {w : List Value} {F : Prop} (hlen : (8#32 : I32).toNat ≤ src.length)
    (hw : w.length = 16) (hF : F) :
    ∃ x, 0#32 = BitVec.ofNat 32 x ∧ x + 8 ≤ rd8Len src ∧ x + 8 < 2147483648 ∧
      ∃ x_1, (rd8Arr src w)[x]? = some (Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
      ∃ x_2, (rd8Arr src w)[x + 1]? = some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      ∃ x_3, (rd8Arr src w)[x + 2]? = some (Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      ∃ x_4, (rd8Arr src w)[x + 3]? = some (Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      ∃ x_5, (rd8Arr src w)[x + 4]? = some (Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      ∃ x_6, (rd8Arr src w)[x + 5]? = some (Value.int (BitVec.signExtend 32 x_6.toBitVec)) ∧
      ∃ x_7, (rd8Arr src w)[x + 6]? = some (Value.int (BitVec.signExtend 32 x_7.toBitVec)) ∧
      ∃ x_8, (rd8Arr src w)[x + 7]? = some (Value.int (BitVec.signExtend 32 x_8.toBitVec)) ∧
      (∃ h : x < rd8Len src,
        (rd8Arr src w)[x]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_1.toBitVec)) ∧
      (∃ h : x + 1 < rd8Len src,
        (rd8Arr src w)[x + 1]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      (∃ h : x + 2 < rd8Len src,
        (rd8Arr src w)[x + 2]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      (∃ h : x + 3 < rd8Len src,
        (rd8Arr src w)[x + 3]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      (∃ h : x + 4 < rd8Len src,
        (rd8Arr src w)[x + 4]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      (∃ h : x + 5 < rd8Len src,
        (rd8Arr src w)[x + 5]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_6.toBitVec)) ∧
      (∃ h : x + 6 < rd8Len src,
        (rd8Arr src w)[x + 6]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_7.toBitVec)) ∧
      (∃ h : x + 7 < rd8Len src,
        (rd8Arr src w)[x + 7]'(rd8_lt hw h) = Value.int (BitVec.signExtend 32 x_8.toBitVec)) ∧
      src = x_1 :: x_2 :: x_3 :: x_4 :: x_5 :: x_6 :: x_7 :: x_8 :: List.drop 8 src ∧ F := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rest, rfl⟩ :
      ∃ u0 u1 u2 u3 u4 u5 u6 u7 rest, src = u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: rest := by
    match src, hlen with
    | u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: rest, _ =>
      exact ⟨u0, u1, u2, u3, u4, u5, u6, u7, rest, rfl⟩
    | [], h => simp at h
    | [_], h => simp at h
    | [_, _], h => simp at h
    | [_, _, _], h => simp at h
    | [_, _, _, _], h => simp at h
    | [_, _, _, _, _], h => simp at h
    | [_, _, _, _, _, _], h => simp at h
    | [_, _, _, _, _, _, _], h => simp at h
  have hk : ∀ k, k < 8 → k < rd8Len (u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: rest) := fun k hk => by
    show k < 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 8)))))))
    omega
  exact ⟨0, rfl, Nat.le_of_ble_eq_true rfl, by decide,
    u0, rfl, u1, rfl, u2, rfl, u3, rfl, u4, rfl, u5, rfl, u6, rfl, u7, rfl,
    ⟨hk 0 (by decide), rfl⟩, ⟨hk 1 (by decide), rfl⟩, ⟨hk 2 (by decide), rfl⟩,
    ⟨hk 3 (by decide), rfl⟩, ⟨hk 4 (by decide), rfl⟩, ⟨hk 5 (by decide), rfl⟩,
    ⟨hk 6 (by decide), rfl⟩, ⟨hk 7 (by decide), rfl⟩, rfl, hF⟩

/-- The buffer fast path: the cut point's facts. -/
theorem ri64_fast_cut {R : TRep} {σ0 : State} {t : Addr} {arr : List Value} {u : UInt8} {rest : Bytes}
    {F : Prop} (hge : ¬ R.bufLen σ0 t < 8)
    (hpl : R.bufPos σ0 t + (R.bufLen σ0 t).toNat ≤ arr.length)
    (heqb : List.take (R.bufLen σ0 t).toNat (List.drop (R.bufPos σ0 t) arr) =
      List.take (R.bufLen σ0 t).toNat (List.map jbyte (R.src σ0 t)))
    (hle : R.bufLen σ0 t ≤ ((R.src σ0 t).length : Int))
    (hlt : R.bufPos σ0 t + (R.bufLen σ0 t).toNat < 2147483648)
    (hsrc0 : R.src σ0 t = u :: rest) (hF : F) :
    ∃ x x_1, BitVec.ofNat 32 (R.bufPos σ0 t) = BitVec.ofNat 32 x_1 ∧ arr = x ∧ x_1 + 8 ≤ x.length ∧
      x_1 + 8 < 2147483648 ∧
      ∃ x_2, x[x_1]? = some (Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      ∃ x_3, x[x_1 + 1]? = some (Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      ∃ x_4, x[x_1 + 2]? = some (Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      ∃ x_5, x[x_1 + 3]? = some (Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      ∃ x_6, x[x_1 + 4]? = some (Value.int (BitVec.signExtend 32 x_6.toBitVec)) ∧
      ∃ x_7, x[x_1 + 5]? = some (Value.int (BitVec.signExtend 32 x_7.toBitVec)) ∧
      ∃ x_8, x[x_1 + 6]? = some (Value.int (BitVec.signExtend 32 x_8.toBitVec)) ∧
      ∃ x_9, x[x_1 + 7]? = some (Value.int (BitVec.signExtend 32 x_9.toBitVec)) ∧
      (∃ h : x_1 < x.length, x[x_1]'h = Value.int (BitVec.signExtend 32 x_2.toBitVec)) ∧
      (∃ h : x_1 + 1 < x.length, x[x_1 + 1]'h = Value.int (BitVec.signExtend 32 x_3.toBitVec)) ∧
      (∃ h : x_1 + 2 < x.length, x[x_1 + 2]'h = Value.int (BitVec.signExtend 32 x_4.toBitVec)) ∧
      (∃ h : x_1 + 3 < x.length, x[x_1 + 3]'h = Value.int (BitVec.signExtend 32 x_5.toBitVec)) ∧
      (∃ h : x_1 + 4 < x.length, x[x_1 + 4]'h = Value.int (BitVec.signExtend 32 x_6.toBitVec)) ∧
      (∃ h : x_1 + 5 < x.length, x[x_1 + 5]'h = Value.int (BitVec.signExtend 32 x_7.toBitVec)) ∧
      (∃ h : x_1 + 6 < x.length, x[x_1 + 6]'h = Value.int (BitVec.signExtend 32 x_8.toBitVec)) ∧
      (∃ h : x_1 + 7 < x.length, x[x_1 + 7]'h = Value.int (BitVec.signExtend 32 x_9.toBitVec)) ∧
      (u = x_2 ∧ rest = x_3 :: x_4 :: x_5 :: x_6 :: x_7 :: x_8 :: x_9 :: List.drop 7 rest) ∧ F := by
  rw [hsrc0] at heqb hle
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, rest', rfl⟩ :
      ∃ v1 v2 v3 v4 v5 v6 v7 rest', rest = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest' := by
    match rest, hle with
    | v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest', _ => exact ⟨v1, v2, v3, v4, v5, v6, v7, rest', rfl⟩
    | [], h => simp at h; omega
    | [_], h => simp at h; omega
    | [_, _], h => simp at h; omega
    | [_, _, _], h => simp at h; omega
    | [_, _, _, _], h => simp at h; omega
    | [_, _, _, _, _], h => simp at h; omega
    | [_, _, _, _, _, _], h => simp at h; omega
  have hL : 8 ≤ (R.bufLen σ0 t).toNat := by omega
  have ek : ∀ k, k < 8 →
      arr[R.bufPos σ0 t + k]? = ((u :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: rest')[k]?).map jbyte := by
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
  have e4 : arr[R.bufPos σ0 t + 4]? = some (Value.int (BitVec.signExtend 32 v4.toBitVec)) := by
    rw [ek 4 (by decide)]
    rfl
  have e5 : arr[R.bufPos σ0 t + 5]? = some (Value.int (BitVec.signExtend 32 v5.toBitVec)) := by
    rw [ek 5 (by decide)]
    rfl
  have e6 : arr[R.bufPos σ0 t + 6]? = some (Value.int (BitVec.signExtend 32 v6.toBitVec)) := by
    rw [ek 6 (by decide)]
    rfl
  have e7 : arr[R.bufPos σ0 t + 7]? = some (Value.int (BitVec.signExtend 32 v7.toBitVec)) := by
    rw [ek 7 (by decide)]
    rfl
  exact ⟨arr, R.bufPos σ0 t, rfl, rfl, by omega, by omega,
    u, e0, v1, e1, v2, e2, v3, e3, v4, e4, v5, e5, v6, e6, v7, e7,
    List.getElem?_eq_some_iff.mp e0, List.getElem?_eq_some_iff.mp e1,
    List.getElem?_eq_some_iff.mp e2, List.getElem?_eq_some_iff.mp e3,
    List.getElem?_eq_some_iff.mp e4, List.getElem?_eq_some_iff.mp e5,
    List.getElem?_eq_some_iff.mp e6, List.getElem?_eq_some_iff.mp e7,
    ⟨rfl, rfl⟩, hF⟩

/-- The return: the value of the eight bytes. -/
theorem ri64_ret_post {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr}
    {u0 u1 u2 u3 u4 u5 u6 u7 : UInt8} {xs : List Value} {c : ClassName} {f0 f1 : List (FieldKey × Value)}
    (hBP : BPAtH P R σ0 p t tmp)
    (hsrc : R.src σ0 t = u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: R.src σ t)
    (hinv : R.inv σ t) (hsink : R.sink σ t = R.sink σ0 t) (hnext : σ0.next ≤ σ.next)
    (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics) (hp : σ.heap p = σ0.heap p)
    (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hxs : xs.length = 16)
    (hop : ¬R.owns σ t p) (hot : ¬R.owns σ t tmp)
    (hfr : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a)
    (ht0 : σ0.heap t = some (.plain c f0)) (ht1 : σ.heap t = some (.plain c f1)) :
    ri64N P R [.ref p] σ0
      (some (.long
        (JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u0.toBitVec) &&& 255#32)) 56#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u1.toBitVec) &&& 255#32)) 48#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u2.toBitVec) &&& 255#32)) 40#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u3.toBitVec) &&& 255#32)) 32#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u4.toBitVec) &&& 255#32)) 24#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u5.toBitVec) &&& 255#32)) 16#32 |||
        JLong.shl (JInt.toLong (JInt.toShort (BitVec.signExtend 32 u6.toBitVec) &&& 255#32)) 8#32 |||
        JInt.toLong (JInt.toShort (BitVec.signExtend 32 u7.toBitVec) &&& 255#32)))) σ := by
  obtain ⟨fs, xs0, c0, fst, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop0, hot0⟩ :=
    BPAtH.elim hBP
  rw [hth] at ht0
  simp only [Option.some.injEq, Obj.plain.injEq] at ht0
  obtain ⟨rfl, -⟩ := ht0
  unfold ri64N
  intro p' t' tmp' hargs hBP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' (BPAtH.elim hBP)
  refine ⟨u0, u1, u2, u3, u4, u5, u6, u7, R.src σ t, _, hsrc, rfl, ri64_val u0 u1 u2 u3 u4 u5 u6 u7, rfl,
    hsink, ?_, ⟨hnext, hin, hst, hfr⟩⟩
  exact ⟨fs, xs, c0, f1, by rw [hp]; exact hph, htr, hte, htmp, hxs, ht1, hc1, hc2, hinv, hpt, htt, hptm,
    hop, hot⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem ri64_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 1
    ri64Ref (fun P => ri64SpecI P R) (ri64Inv R) 100 := by
  jverify_body [Contains, BPAt, ClassOK, ri64SpecI, ri64Inv, tc_write, tc_readAll,
    tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, BufView, TFrame, jbyte, ofNat_succ32, ttCls, bpCls, tpCls]
  case left.some.true.normal.isTrue.left => exact br_readAll_pre R ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case left.some.true.normal.isTrue.right.normal =>
    exact ri64_slow_cut ‹_› ‹_› (rdFrame_slow ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (slow_len ‹_› ‹_› (by decide)) ‹_›
      ‹_› ‹_› ‹_›)
  case left.some.true.normal.isTrue.right.exc => exact ri64_exc_post ‹_› ‹_› ‹_›
  case left.some.true.normal.isFalse.right.normal.right.normal.right.normal =>
    exact ri64_fast_cut ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (rdFrame_fast ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case right.isTrue.isTrue.isTrue =>
    exact ri64_ret_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

theorem ri64_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P ri64Ref (ri64Spec P R) := by
  have hI := BodyVCP.sat (ri64_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, hargs, hBP, BPAtH.intro hBP, classOK_of_bpAt hBP⟩ hm

theorem readI64_cons (u0 u1 u2 u3 u4 u5 u6 u7 : UInt8) (rest : Spec.Bytes) :
    Spec.readI64 (u0 :: u1 :: u2 :: u3 :: u4 :: u5 :: u6 :: u7 :: rest) =
      some (Spec.toS 64 (2 ^ 56 * u0.toNat + 2 ^ 48 * u1.toNat + 2 ^ 40 * u2.toNat + 2 ^ 32 * u3.toNat +
        2 ^ 24 * u4.toNat + 2 ^ 16 * u5.toNat + 2 ^ 8 * u6.toNat + u7.toNat), rest) := by
  simp only [Spec.readI64, Spec.readBE, Spec.beVal, Spec.Truncated]
  simp only [List.length_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.foldl_cons, List.foldl_nil]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  omega

/-- **D for binary i64**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `readI64()` on a source `Spec.beI64 v ++ rest` (any `i64`
value `v`) returns `v` and leaves `rest`. -/
theorem ri64_D {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (v : Int) (hv : Spec.InI64 v) (rest : Spec.Bytes) (hsrc : R.src σ t = Spec.beI64 v ++ rest)
    {o : Outcome} (hm : MExec P ri64Ref [.ref p] σ o) :
    ∃ σ', o = .normal (some (.long (BitVec.ofInt 64 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := ri64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri64Spec, Spec.of] at hpost
    unfold ri64N at hpost
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rest', x, hs, hr, hx, hs', hsink, hBP', -⟩ :=
      hpost p t tmp rfl hBP
    have h1 := Spec.readI64_beI64 hv rest
    rw [← hsrc, hs, readI64_cons] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv', hr'⟩ := h1
    refine ⟨σ', by rw [hr, ← hx.trans hv', BitVec.ofInt_toInt], by rw [hs', hr'], hsink, hBP'⟩
  | exc e σ' =>
    simp only [ri64Spec, Spec.of] at hpost
    unfold ri64E at hpost
    obtain ⟨hlen, -⟩ := hpost p t tmp rfl hBP
    rw [hsrc, List.length_append, Spec.beI64, Spec.be_length] at hlen
    omega
  | wrong msg => simp only [ri64Spec, Spec.of] at hpost

/-- **M for binary i64**: on fewer than eight bytes, `readI64()` throws a `TTransportException` (the
transport's, from `readAll`); `Spec.readI64` is `none` exactly there. -/
theorem ri64_M {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (hshort : (R.src σ t).length < 8) {o : Outcome} (hm : MExec P ri64Ref [.ref p] σ o) :
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) := by
  have hpost := ri64_sat R hF hV [.ref p] σ o ⟨p, t, tmp, rfl, hBP⟩ hm
  cases o with
  | normal r σ' =>
    simp only [ri64Spec, Spec.of] at hpost
    unfold ri64N at hpost
    obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, rest', x, hs, -⟩ := hpost p t tmp rfl hBP
    rw [hs] at hshort
    simp only [List.length_cons] at hshort
    omega
  | exc e σ' =>
    simp only [ri64Spec, Spec.of] at hpost
    unfold ri64E at hpost
    obtain ⟨-, hexc⟩ := hpost p t tmp rfl hBP
    exact ⟨e, σ', rfl, hexc⟩
  | wrong msg => simp only [ri64Spec, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
