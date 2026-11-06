import EquivLean.Demo.Thrift.Java.Lem

/-!
# Thrift → Java (T4): `TCompactProtocol.writeVarint64(long)` appends the varint (E)

Two cut points: the loop head (statement 3) and statement 4, after `$l0 = n & -128L`. The second one
names the masked value `v` (with `v = 0 ↔ n < 128`): run as one path, statements 3 to 5 (the mask,
then `lcmp`) leave the kernel a definitional check on `n &&& -128L` that it does not finish ("deep
recursion"), at any `maxRecDepth`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev wv64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeVarint64(long)».ref

/-- What `writeVarint64(n)` guarantees: it appends `varint (toU 64 n)` to the transport. -/
def wv64N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] → CPAt P R σ p t tmp →
    r = none ∧ CPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.varint n.toNat ∧
    R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

attribute [irreducible] wv64N

/-- **E for varint64**. -/
def wv64Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] ∧ CPAt P R σ p t tmp)
  (wv64N P R)
  (fun _ _ _ _ => False)

/-- The contract with a hidden copy of the protocol facts, for the proof. -/
def wv64SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp)
  (wv64N P R)
  (fun _ _ _ _ => False)

/-- Statement 3 (the loop head): the first `i` bytes of the varint are in `temp`, `n` holds the
rest `x`; statement 4: also `$l0 = v` with `v = 0` exactly when `x < 128`. -/
def wv64Inv : Invariants := [(3, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I64) (fs : List (FieldKey × Value)), args = [.ref p, .long n0] →
  σ0.heap p = some (.plain cpCls fs) → Fields.get fs (cpCls, "temp") = some (.ref tmp) →
  ∃ (i : Nat) (x : I64) (xs : List Value), fr.get 8 = some (.ref p) ∧
    fr.get 2 = some (.long x) ∧ fr.get 7 = some (.int (BitVec.ofNat 32 i)) ∧ i ≤ 9 ∧
    x.toNat < 2 ^ (64 - 7 * i) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take i).map byteOf ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a)),
  (4, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I64) (fs : List (FieldKey × Value)), args = [.ref p, .long n0] →
  σ0.heap p = some (.plain cpCls fs) → Fields.get fs (cpCls, "temp") = some (.ref tmp) →
  ∃ (i : Nat) (x v : I64) (xs : List Value), fr.get 8 = some (.ref p) ∧
    fr.get 2 = some (.long x) ∧ fr.get 1 = some (.long v) ∧ fr.get 7 = some (.int (BitVec.ofNat 32 i)) ∧
    i ≤ 9 ∧ x.toNat < 2 ^ (64 - 7 * i) ∧ (v = 0#64 ↔ x.toNat < 128) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take i).map byteOf ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a)),
  (6, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I64) (fs : List (FieldKey × Value)), args = [.ref p, .long n0] →
  σ0.heap p = some (.plain cpCls fs) → Fields.get fs (cpCls, "temp") = some (.ref tmp) →
  ∃ (i : Nat) (x : I64) (xs : List Value), fr.get 8 = some (.ref p) ∧
    fr.get 2 = some (.long x) ∧ fr.get 7 = some (.int (BitVec.ofNat 32 i)) ∧ i ≤ 9 ∧ x.toNat < 128 ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take i).map byteOf ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a)),
  (22, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I64) (fs : List (FieldKey × Value)), args = [.ref p, .long n0] →
  σ0.heap p = some (.plain cpCls fs) → Fields.get fs (cpCls, "temp") = some (.ref tmp) →
  ∃ (k : Nat) (xs : List Value), fr.get 8 = some (.ref p) ∧
    fr.get 6 = some (.int (BitVec.ofNat 32 k)) ∧ 1 ≤ k ∧ k ≤ 10 ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take k).map byteOf = Spec.varint n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a))]

/-! ## Bit facts of the `long` operations -/

theorem mask64_bits : ∀ i, i < 64 → (18446744073709551488#64).getLsbD i = decide (7 ≤ i) := by decide

theorem and_mask64_eq (x : I64) : x &&& 18446744073709551488#64 = (x >>> 7) <<< 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, mask64_bits i hi, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : 7 ≤ i
  · have e : 7 + (i - 7) = i := by omega
    simp [h, hi, e, show ¬ i < 7 by omega]
  · simp [h, show i < 7 by omega]

/-- `n & ~0x7FL == 0`: the value fits in 7 bits. -/
theorem and_m128_eq_zero64 (x : I64) : (x &&& 18446744073709551488#64 = 0#64) ↔ x.toNat < 128 := by
  rw [and_mask64_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight] at this
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat] at this
    have hx := x.isLt
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega

theorem lushr7_toNat (x : I64) : (JLong.ushr x 7#32).toNat = x.toNat / 128 := by
  simp only [JLong.ushr]
  rw [BitVec.toNat_ushiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem cont64_toNat (x : I64) : (x &&& 127#64 ||| 128#64).toNat = x.toNat % 128 + 128 := by
  have e : x &&& 127#64 ||| 128#64 = (x &&& 127#64) + 128#64 := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    rw [BitVec.and_assoc, show (127#64 &&& 128#64 : I64) = 0#64 by decide, BitVec.and_zero]
  rw [e, BitVec.toNat_add, BitVec.toNat_and, show (127#64).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  have : x.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  simp only [show (128#64).toNat = 128 from rfl]
  omega

theorem l2i_toNat (x : I64) : (JLong.toInt x).toNat = x.toNat % 2 ^ 32 := by
  simp only [JLong.toInt, BitVec.toNat_setWidth]

/-- The continuation byte `(byte) (int) ((n & 0x7FL) | 0x80L)`. -/
theorem byteOf_cont64 (x : I64) :
    byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (x &&& 127#64 ||| 128#64))))) =
      UInt8.ofNat (x.toNat % 128 + 128) := by
  rw [toByte_toByte, byteOf_toByte, l2i_toNat, cont64_toNat]
  have : x.toNat % 128 + 128 < 2 ^ 32 := by have := Nat.mod_lt x.toNat (show 128 > 0 by decide); omega
  rw [Nat.mod_eq_of_lt this]

/-- The last byte `(byte) (int) n`, for `n < 128`. -/
theorem byteOf_last64 (x : I64) (h : x.toNat < 128) :
    byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt x)))) = UInt8.ofNat x.toNat := by
  rw [toByte_toByte, byteOf_toByte, l2i_toNat, Nat.mod_eq_of_lt (by omega)]

/-! ## The paths between the cut points -/

theorem wv64_entry {n0 : I64} {xs : List Value} : ∃ x, 0#32 = BitVec.ofNat 32 x ∧ x ≤ 9 ∧
    n0.toNat < 2 ^ (64 - 7 * x) ∧ (x = 0 ∨ xs = []) :=
  ⟨0, rfl, by omega, by simpa using n0.isLt, Or.inl rfl⟩

/-- Statement 3 to statement 4: the mask. -/
theorem wv64_to4 {i : Nat} {x n0 : I64} {xs : List Value} {σ σ0 : State} {tmp : Addr}
    (hi : i ≤ 9) (hx : x.toNat < 2 ^ (64 - 7 * i))
    (heq : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat)
    (hfr : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) :
    ∃ i', BitVec.ofNat 32 i = BitVec.ofNat 32 i' ∧ i' ≤ 9 ∧ x.toNat < 2 ^ (64 - 7 * i') ∧
      (x &&& 18446744073709551488#64 = 0#64 ↔ x.toNat < 128) ∧
      List.take i' (List.map byteOf xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
      ∀ a, ¬a = tmp → σ.heap a = σ0.heap a :=
  ⟨i, rfl, hi, hx, and_m128_eq_zero64 x, by rw [List.map_take] at heq; exact heq, hfr⟩

/-- Statement 4 to statement 6 (the last byte comes next). -/
theorem wv64_to6 {i : Nat} {x n0 : I64} {xs : List Value} {σ σ0 : State} {tmp : Addr}
    (hi : i ≤ 9) (heq : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat)
    (hfr : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) :
    ∃ i', BitVec.ofNat 32 i = BitVec.ofNat 32 i' ∧ i' ≤ 9 ∧
      List.take i' (List.map byteOf xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat ∧
      ∀ a, ¬a = tmp → σ.heap a = σ0.heap a :=
  ⟨i, rfl, hi, by rw [List.map_take] at heq; exact heq, hfr⟩

theorem nlt128_of_neg {v x : I64} (hiff : v = 0#64 ↔ x.toNat < 128) (hv : v.toInt < 0) :
    ¬ x.toNat < 128 := fun h => by
  rw [hiff.mpr h] at hv
  exact absurd hv (by decide)

/-- The loop step (statement 4 back to 3): one more continuation byte. -/
theorem wv64_step {x n0 : I64} {i : Nat} {xs : List Value} {tmp : Addr} {σ0 : State}
    (hge : ¬ x.toNat < 128) (hi : i ≤ 9) (hx : x.toNat < 2 ^ (64 - 7 * i)) (hlen : xs.length = 16)
    (heq : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat) :
    ∃ i', BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 i' ∧ i' ≤ 9 ∧
      (JLong.ushr x 7#32).toNat < 2 ^ (64 - 7 * i') ∧
      List.take i' ((List.map byteOf xs).set i
          (byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (x &&& 127#64 ||| 128#64))))))) ++
        Spec.varint (JLong.ushr x 7#32).toNat = Spec.varint n0.toNat ∧
      ∀ a, ¬a = tmp → a = tmp →
        some (Obj.array (.prim .byte)
          (xs.set i (.int (JInt.toByte (JInt.toByte (JLong.toInt (x &&& 127#64 ||| 128#64))))))) =
          σ0.heap a := by
  have hi8 : i ≤ 8 := by
    rcases Nat.lt_or_ge i 9 with h | h
    · omega
    · have h9 : i = 9 := by omega
      subst h9
      rw [show 2 ^ (64 - 7 * 9) = 2 by decide] at hx
      omega
  have hpow : 2 ^ (64 - 7 * i) = 2 ^ (64 - 7 * (i + 1)) * 128 := by
    rw [show 64 - 7 * i = (64 - 7 * (i + 1)) + 7 by omega, Nat.pow_add]
  refine ⟨i + 1, ofNat_succ32 i, by omega, ?_, ?_, fun a h1 h2 => absurd h2 h1⟩
  · rw [lushr7_toNat, Nat.div_lt_iff_lt_mul (by decide), ← hpow]
    exact hx
  · rw [List.map_take] at heq
    rw [lushr7_toNat, take_set_succ _ _ _ (by rw [List.length_map, hlen]; omega), byteOf_cont64,
      List.append_assoc, List.singleton_append, ← heq, Spec.varint_eq x.toNat, ite_eq_right hge]

/-- Statement 6 to statement 22 (label3): the last byte. -/
theorem wv64_to22 {x n0 : I64} {i : Nat} {xs : List Value} {tmp : Addr} {σ0 : State}
    (hlt : x.toNat < 128) (hi : i ≤ 9) (hlen : xs.length = 16)
    (heq : List.map byteOf (List.take i xs) ++ Spec.varint x.toNat = Spec.varint n0.toNat) :
    ∃ k, BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 k ∧ 1 ≤ k ∧ k ≤ 10 ∧
      List.take k ((List.map byteOf xs).set i (byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt x)))))) =
        Spec.varint n0.toNat ∧
      ∀ a, ¬a = tmp → a = tmp →
        some (Obj.array (.prim .byte) (xs.set i (.int (JInt.toByte (JInt.toByte (JLong.toInt x)))))) =
          σ0.heap a := by
  refine ⟨i + 1, ofNat_succ32 i, by omega, by omega, ?_, fun a h1 h2 => absurd h2 h1⟩
  rw [List.map_take] at heq
  rw [take_set_succ _ _ _ (by rw [List.length_map, hlen]; omega), byteOf_last64 x hlt, ← heq,
    Spec.varint_eq x.toNat, ite_eq_left hlt]

/-- The call of `write` at statement 24: its precondition. -/
theorem wv64_exit_pre (R : TRep) {σ0 σ : State} {t tmp : Addr} {xs : List Value} {k : Nat}
    (hinv : R.inv σ0 t) (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) (hnext : σ.next = σ0.next)
    (ht : tmp ≠ t) (ho : ¬ R.owns σ0 t tmp) (htmp : σ.heap tmp = some (.array (.prim .byte) xs))
    (hlen : xs.length = 16) (hk : k ≤ 10) :
    ∃ t' buf off len, (t = t' ∧ tmp = buf ∧ 0#32 = off ∧ BitVec.ofNat 32 k = len) ∧ R.inv σ t' ∧
      ∃ x, σ.heap buf = some (.array (.prim .byte) x) ∧
        0 ≤ BitVec.toInt off ∧ 0 ≤ BitVec.toInt len ∧ BitVec.toInt off + BitVec.toInt len ≤ x.length ∧
        ¬buf = t' ∧ ¬R.owns σ t' buf := by
  obtain ⟨hinvσ, -, -, -, -, -, howσ⟩ := rep_scratch R hinv heq (Nat.le_of_eq hnext.symm) ht ho
  refine ⟨t, tmp, 0#32, BitVec.ofNat 32 k, ⟨rfl, rfl, rfl, rfl⟩, hinvσ, xs, htmp, by decide, ?_, ?_, ht,
    by rw [howσ]; exact ho⟩
  · rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    split <;> omega
  · rw [show (0#32 : I32).toInt = 0 from rfl, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, hlen]
    split <;> omega

/-- The return: the transport got the varint. -/
theorem wv64_exit_post {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {n0 : I64} {k : Nat}
    {xs : List Value}
    (hCP : CPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16) (hk : k ≤ 10)
    (heqv : List.map byteOf (List.take k xs) = Spec.varint n0.toNat) (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t ++
      List.take (BitVec.ofNat 32 k).toNat (List.drop (0#32).toNat (List.map byteOf xs)))
    (hsrc : R.src σ' t = R.src σ t) (hf : TFrame R σ σ' t t) :
    wv64N P R [.ref p, .long n0] σ0 none σ' := by
  unfold wv64N
  intro p' t' tmp' n' he hCP'
  simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' hCP
  have hCPσ : CPAt P R σ p t tmp := cpAt_scratch hCP hheap (Nat.le_of_eq hnext.symm) htmpσ hlen
  obtain ⟨fs, xs0, c, fst, hph, -, -, htmh, -, -, -, -, hinv0, hpt, htt, hptm, hop, hot⟩ := hCP
  obtain ⟨hCP', hfr⟩ := cpAt_call hCPσ hf hinv' hpt htt
  obtain ⟨-, hs0, hr0, -, -, -, how0⟩ := rep_scratch R hinv0 hheap (Nat.le_of_eq hnext.symm) htt hot
  have hk1 : (BitVec.ofNat 32 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    omega
  obtain ⟨hn', hin', hst', -, -, -⟩ := hf
  refine ⟨rfl, hCP', ?_, by rw [hsrc, hr0], ?_, ?_, ?_, ?_⟩
  · rw [hsink, hs0, hk1, show (0#32 : I32).toNat = 0 from rfl, List.drop_zero, ← List.map_take, heqv]
  · rw [← hnext]
    exact hn'
  · rw [hin']
    exact hin
  · rw [hst']
    exact hst
  · intro a ha hat hatm hao
    rw [hfr a (by rw [hnext]; exact ha) hat (by rw [how0]; exact hao) hat, hheap a hatm]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wv64_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    wv64Ref (fun P => wv64SpecI P R) wv64Inv 60 := by
  jverify_body [Contains, tContracts, CPAt, PFrame, wv64SpecI, wv64Inv, writeSpec, writeSig, ttCls,
    cpCls, tpCls]
  case left => exact wv64_entry
  case right.left => exact wv64_to4 ‹_› ‹_› ‹_› ‹_›
  case right.right.left.isTrue.isTrue => exact wv64_step (nlt128_of_neg ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_›
  case right.right.left.isFalse.isTrue => exact wv64_to6 ‹_› ‹_› ‹_›
  case right.right.left.isFalse.isFalse.isTrue => exact wv64_step ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.right.left.isTrue => exact wv64_to22 ‹_› ‹_› ‹_› ‹_›
  case right.right.right.right.some.some.true.left =>
    exact wv64_exit_pre R ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.right.right.some.some.true.right.normal =>
    exact wv64_exit_post (CPAtH.elim ‹CPAtH _ R _ _ _ _›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (by unfold TFrame; exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩)

/-! ## The result -/

theorem wv64_toU64_toInt (x : I64) : Spec.toU 64 x.toInt = x.toNat := by
  have hx := x.isLt
  have hc := BitVec.toInt_eq_toNat_cond x
  have key : ((Spec.toU 64 x.toInt : Nat) : Int) = (x.toNat : Int) := by
    by_cases h : 2 * x.toNat < 2 ^ 64
    · rw [ite_eq_left h] at hc
      rw [Spec.toU_of_nonneg (by rw [hc]; omega) (by rw [hc]; simp; omega), hc]
    · rw [ite_eq_right h] at hc
      rw [Spec.toU_of_neg (by rw [hc]; simp at h ⊢; omega) (by rw [hc]; simp; omega), hc]
      simp
  exact_mod_cast key

theorem wv64_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wv64Ref (wv64Spec P R) := by
  have hI := BodyVCP.sat (wv64_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, n, hargs, hCP, CPAtH.intro hCP⟩ hm

/-- **E for varint64**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `writeVarint64(x)` returns normally after appending
`Spec.varint (toU 64 x)` to the transport. -/
theorem wv64_E {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (x : I64) {o : Outcome} (hm : MExec P wv64Ref [.ref p, .long x] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.varint (Spec.toU 64 x.toInt) ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp := by
  have hpost := wv64_sat R hF hV [.ref p, .long x] σ o ⟨p, t, tmp, x, rfl, hCP⟩ hm
  rw [wv64_toU64_toInt]
  cases o with
  | normal r σ' =>
    simp only [wv64Spec, Spec.of] at hpost
    unfold wv64N at hpost
    obtain ⟨hr, hC, hs, hsrc, -⟩ := hpost p t tmp x rfl hCP
    exact ⟨σ', by rw [hr], hs, hsrc, hC⟩
  | exc e σ' => simp only [wv64Spec, Spec.of] at hpost
  | wrong msg => simp only [wv64Spec, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
