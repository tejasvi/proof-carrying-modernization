import EquivLean.Demo.Thrift.Java.Bp

/-!
# Thrift → Java (T4): `TBinaryProtocol.writeI16/writeI32/writeI64` append the big-endian bytes (E)

Each writer stores the bytes into `inoutTemp`, then calls `trans_.write(inoutTemp, 0, k)`. One cut
point, at the load of `trans_` before the call: the first `k` bytes of `inoutTemp` are the bytes.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-! ## The bytes: `(byte) ((x >> s) & 0xFF)` -/

theorem l2i_toNat' (x : I64) : (JLong.toInt x).toNat = x.toNat % 2 ^ 32 := by
  simp only [JLong.toInt, BitVec.toNat_setWidth]

theorem uint8_ofNat_mod (a : Nat) : UInt8.ofNat (a % 256) = UInt8.ofNat a := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 256 from rfl]
  omega

/-- The low byte of `0xFF & v`, as a Java `byte` element. -/
theorem byteOf_mask255 (v : I32) :
    byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& v)))) = UInt8.ofNat v.toNat := by
  rw [toByte_toByte, byteOf_toByte, BitVec.toNat_and, show (255#32 : I32).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, show (2 : Nat) ^ 8 = 256 from rfl, uint8_ofNat_mod]

/-- The low byte of `(int) (0xFFL & v)`, as a Java `byte` element. -/
theorem byteOf_mask255L (v : I64) :
    byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& v))))) = UInt8.ofNat v.toNat := by
  rw [toByte_toByte, byteOf_toByte, l2i_toNat', BitVec.toNat_and, show (255#64 : I64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  rw [show v.toNat % 2 ^ 8 % 2 ^ 32 = v.toNat % 256 by
    rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt v.toNat (show 2 ^ 8 > 0 by decide); omega)],
    uint8_ofNat_mod]

/-- The low 8 bits of an arithmetic right shift by `s ≤ 24` are bits `s..s+7`. -/
theorem sshr_low8 (n : I32) (s : Nat) (hs : s ≤ 24) : (n.sshiftRight s).toNat % 256 = n.toNat / 2 ^ s % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, BitVec.testBit_toNat,
    BitVec.getLsbD_sshiftRight, Nat.testBit_div_two_pow, ← BitVec.testBit_toNat]
  by_cases hi : i < 8
  · simp [hi, show i < 32 by omega, show s + i < 32 by omega, Nat.add_comm]
  · simp [hi]

theorem sshr_low8L (n : I64) (s : Nat) (hs : s ≤ 56) : (n.sshiftRight s).toNat % 256 = n.toNat / 2 ^ s % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, BitVec.testBit_toNat,
    BitVec.getLsbD_sshiftRight, Nat.testBit_div_two_pow, ← BitVec.testBit_toNat]
  by_cases hi : i < 8
  · simp [hi, show i < 64 by omega, show s + i < 64 by omega, Nat.add_comm]
  · simp [hi]

theorem ofNat_shr (n : I32) (s : Nat) (hs : s ≤ 24) :
    UInt8.ofNat (JInt.shr n (BitVec.ofNat 32 s)).toNat = UInt8.ofNat (n.toNat / 2 ^ s) := by
  have e : JInt.shr n (BitVec.ofNat 32 s) = n.sshiftRight s := by
    simp only [JInt.shr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt (by omega : s < 32)]
  rw [e, ← uint8_ofNat_mod, sshr_low8 n s hs, uint8_ofNat_mod]

theorem ofNat_shrL (n : I64) (s : Nat) (hs : s ≤ 56) :
    UInt8.ofNat (JLong.shr n (BitVec.ofNat 32 s)).toNat = UInt8.ofNat (n.toNat / 2 ^ s) := by
  have e : JLong.shr n (BitVec.ofNat 32 s) = n.sshiftRight s := by
    simp only [JLong.shr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt (by omega : s < 64)]
  rw [e, ← uint8_ofNat_mod, sshr_low8L n s hs, uint8_ofNat_mod]

/-! ## The end of a writer: the call of `write` -/

/-- The call `write(inoutTemp, 0, k)`: its precondition. -/
theorem bw_exit_pre (R : TRep) {σ0 σ : State} {t tmp : Addr} {xs : List Value} {k : Nat}
    (hinv : R.inv σ0 t) (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) (hnext : σ.next = σ0.next)
    (ht : tmp ≠ t) (ho : ¬ R.owns σ0 t tmp) (htmp : σ.heap tmp = some (.array (.prim .byte) xs))
    (hlen : xs.length = 16) (hk : k ≤ 16) :
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

/-- After the call: the transport got the first `k` bytes of `inoutTemp`. -/
theorem bw_exit_core {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {k : Nat}
    {xs : List Value} {bytes : Bytes}
    (hBP : BPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16) (hk : k ≤ 16)
    (hbytes : List.map byteOf (List.take k xs) = bytes) (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t ++
      List.take (BitVec.ofNat 32 k).toNat (List.drop (0#32).toNat (List.map byteOf xs)))
    (hsrc : R.src σ' t = R.src σ t) (hf : TFrame R σ σ' t t) :
    BPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ0 t ++ bytes ∧ R.src σ' t = R.src σ0 t ∧
      PFrame R σ0 σ' t tmp := by
  have hBPσ : BPAt P R σ p t tmp := bpAt_scratch hBP hheap (Nat.le_of_eq hnext.symm) htmpσ hlen
  obtain ⟨fs, xs0, c, fst, hph, -, -, htmh, -, -, -, -, hinv0, hpt, htt, hptm, hop, hot⟩ := hBP
  obtain ⟨hBP', hfr⟩ := bpAt_call hBPσ hf hinv' hpt htt
  obtain ⟨-, hs0, hr0, -, -, -, how0⟩ := rep_scratch R hinv0 hheap (Nat.le_of_eq hnext.symm) htt hot
  have hk1 : (BitVec.ofNat 32 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    omega
  obtain ⟨hn', hin', hst', -, -, -⟩ := hf
  refine ⟨hBP', ?_, by rw [hsrc, hr0], ?_, ?_, ?_, ?_⟩
  · rw [hsink, hs0, hk1, show (0#32 : I32).toNat = 0 from rfl, List.drop_zero, ← List.map_take, hbytes]
  · rw [← hnext]
    exact hn'
  · rw [hin']
    exact hin
  · rw [hst']
    exact hst
  · intro a ha hat hatm hao
    rw [hfr a (by rw [hnext]; exact ha) hat (by rw [how0]; exact hao) hat, hheap a hatm]

/-! ## `writeI16(short)` -/

abbrev bwi16Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«writeI16(short)».ref

/-- What `writeI16(n)` guarantees: it appends the two low bytes of `n`, big-endian. -/
def bwi16N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] → BPAt P R σ p t tmp →
    r = none ∧ BPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.be 2 n.toNat ∧
    R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

attribute [irreducible] bwi16N

def wi16Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ BPAt P R σ p t tmp)
  (bwi16N P R)
  (fun _ _ _ _ => False)

def bwi16SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ BPAt P R σ p t tmp ∧
     BPAtH P R σ p t tmp)
  (bwi16N P R)
  (fun _ _ _ _ => False)

/-- Statement 12 (the load of `trans_`): the two bytes are in `inoutTemp`. -/
def wi16Inv : Invariants := [(12, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I32) (fs : List (FieldKey × Value)), args = [.ref p, .int n0] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (xs : List Value), fr.get 5 = some (.ref p) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take 2).map byteOf = Spec.be 2 n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a))]

theorem wi16_bytes (n : I32) :
    [byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& JInt.shr n 8#32)))),
      byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& n))))] = Spec.be 2 n.toNat := by
  rw [byteOf_mask255, byteOf_mask255, Spec.be_two, ofNat_shr n 8 (by decide)]

theorem wi16_exit_post {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {n0 : I32}
    {xs : List Value}
    (hBP : BPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (hbytes : List.map byteOf (List.take 2 xs) = Spec.be 2 n0.toNat) (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t ++
      List.take (BitVec.ofNat 32 2).toNat (List.drop (0#32).toNat (List.map byteOf xs)))
    (hsrc : R.src σ' t = R.src σ t) (hf : TFrame R σ σ' t t) :
    bwi16N P R [.ref p, .int n0] σ0 none σ' := by
  unfold bwi16N
  intro p' t' tmp' n' he hBP'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hBP
  obtain ⟨h1, h2, h3, h4⟩ :=
    bw_exit_core hBP hheap hnext hin hst htmpσ hlen (by decide) hbytes hinv' hsink hsrc hf
  exact ⟨rfl, h1, h2, h3, h4⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem bwi16_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    bwi16Ref (fun P => bwi16SpecI P R) wi16Inv 60 := by
  jverify_body [Contains, tContracts, BPAt, PFrame, bwi16SpecI, wi16Inv, writeSpec, writeSig, ttCls,
    bpCls, tpCls]
  case left.left => exact wi16_bytes _
  case right.some.some.true.left => exact bw_exit_pre R ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case right.some.some.true.right.normal =>
    exact wi16_exit_post (BPAtH.elim ‹BPAtH _ R _ _ _ _›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (by unfold TFrame; exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩)

theorem wi16_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P bwi16Ref (wi16Spec P R) := by
  have hI := BodyVCP.sat (bwi16_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩ hm

theorem be2_toU16 (x : I32) : Spec.beI16 x.toInt = Spec.be 2 x.toNat := by
  have hx := x.isLt
  have hu : Spec.toU 16 x.toInt = x.toNat % 65536 := by
    have h1 : x.toInt % (65536 : Int) = ((x.toNat % 65536 : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]
      split <;> omega
    show (x.toInt % ((2 ^ 16 : Nat) : Int)).toNat = _
    rw [show ((2 ^ 16 : Nat) : Int) = 65536 from rfl, h1, Int.toNat_natCast]
  rw [Spec.beI16, hu, Spec.be_two, Spec.be_two]
  have e1 : UInt8.ofNat (x.toNat % 65536 / 2 ^ 8) = UInt8.ofNat (x.toNat / 2 ^ 8) := by
    rw [← uint8_ofNat_mod (x.toNat % 65536 / 2 ^ 8), ← uint8_ofNat_mod (x.toNat / 2 ^ 8),
      show (2 : Nat) ^ 8 = 256 from rfl]
    congr 1
    omega
  have e2 : UInt8.ofNat (x.toNat % 65536) = UInt8.ofNat x.toNat := by
    rw [← uint8_ofNat_mod (x.toNat % 65536), ← uint8_ofNat_mod x.toNat]
    congr 1
    omega
  rw [e1, e2]

/-- **E for binary i16**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `writeI16(x)` returns normally after appending
`Spec.beI16 x` (the two bytes of `x`, big-endian). -/
theorem wi16_E {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (x : I32) {o : Outcome} (hm : MExec P bwi16Ref [.ref p, .int x] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI16 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := wi16_sat R hF hV [.ref p, .int x] σ o ⟨p, t, tmp, x, rfl, hBP⟩ hm
  rw [be2_toU16]
  cases o with
  | normal r σ' =>
    simp only [wi16Spec, Spec.of] at hpost
    unfold bwi16N at hpost
    obtain ⟨hr, hC, hs, hsrc, -⟩ := hpost p t tmp x rfl hBP
    exact ⟨σ', by rw [hr], hs, hsrc, hC⟩
  | exc e σ' => simp only [wi16Spec, Spec.of] at hpost
  | wrong msg => simp only [wi16Spec, Spec.of] at hpost

/-! ## `writeI32(int)` -/

abbrev wi32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«writeI32(int)».ref

/-- What `writeI32(n)` guarantees: it appends the four bytes of `n`, big-endian. -/
def wi32N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] → BPAt P R σ p t tmp →
    r = none ∧ BPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.be 4 n.toNat ∧
    R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

attribute [irreducible] wi32N

def wi32Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ BPAt P R σ p t tmp)
  (wi32N P R)
  (fun _ _ _ _ => False)

def wi32SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ BPAt P R σ p t tmp ∧
     BPAtH P R σ p t tmp)
  (wi32N P R)
  (fun _ _ _ _ => False)

/-- Statement 21 (the load of `trans_`): the four bytes are in `inoutTemp`. -/
def wi32Inv : Invariants := [(21, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I32) (fs : List (FieldKey × Value)), args = [.ref p, .int n0] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (xs : List Value), fr.get 5 = some (.ref p) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take 4).map byteOf = Spec.be 4 n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a))]

theorem wi32_bytes (n : I32) :
    [byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& JInt.shr n 24#32)))),
      byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& JInt.shr n 16#32)))),
      byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& JInt.shr n 8#32)))),
      byteOf (.int (JInt.toByte (JInt.toByte (255#32 &&& n))))] = Spec.be 4 n.toNat := by
  rw [byteOf_mask255, byteOf_mask255, byteOf_mask255, byteOf_mask255, Spec.be_four,
    ofNat_shr n 24 (by decide), ofNat_shr n 16 (by decide), ofNat_shr n 8 (by decide)]

theorem wi32_exit_post {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {n0 : I32}
    {xs : List Value}
    (hBP : BPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (hbytes : List.map byteOf (List.take 4 xs) = Spec.be 4 n0.toNat) (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t ++
      List.take (BitVec.ofNat 32 4).toNat (List.drop (0#32).toNat (List.map byteOf xs)))
    (hsrc : R.src σ' t = R.src σ t) (hf : TFrame R σ σ' t t) :
    wi32N P R [.ref p, .int n0] σ0 none σ' := by
  unfold wi32N
  intro p' t' tmp' n' he hBP'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hBP
  obtain ⟨h1, h2, h3, h4⟩ :=
    bw_exit_core hBP hheap hnext hin hst htmpσ hlen (by decide) hbytes hinv' hsink hsrc hf
  exact ⟨rfl, h1, h2, h3, h4⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi32_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    wi32Ref (fun P => wi32SpecI P R) wi32Inv 60 := by
  jverify_body [Contains, tContracts, BPAt, PFrame, wi32SpecI, wi32Inv, writeSpec, writeSig, ttCls,
    bpCls, tpCls]
  case left.left => exact wi32_bytes _
  case right.some.some.true.left => exact bw_exit_pre R ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case right.some.some.true.right.normal =>
    exact wi32_exit_post (BPAtH.elim ‹BPAtH _ R _ _ _ _›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (by unfold TFrame; exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩)

theorem wi32_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wi32Ref (wi32Spec P R) := by
  have hI := BodyVCP.sat (wi32_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩ hm

theorem bw_toU32_toInt (x : I32) : Spec.toU 32 x.toInt = x.toNat := by
  have hx := x.isLt
  have h1 : x.toInt % (4294967296 : Int) = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  show (x.toInt % ((2 ^ 32 : Nat) : Int)).toNat = _
  rw [show ((2 ^ 32 : Nat) : Int) = 4294967296 from rfl, h1, Int.toNat_natCast]

/-- **E for binary i32**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `writeI32(x)` returns normally after appending
`Spec.beI32 x` (the four bytes of `x`, big-endian). -/
theorem wi32_E {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (x : I32) {o : Outcome} (hm : MExec P wi32Ref [.ref p, .int x] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI32 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := wi32_sat R hF hV [.ref p, .int x] σ o ⟨p, t, tmp, x, rfl, hBP⟩ hm
  rw [Spec.beI32, bw_toU32_toInt]
  cases o with
  | normal r σ' =>
    simp only [wi32Spec, Spec.of] at hpost
    unfold wi32N at hpost
    obtain ⟨hr, hC, hs, hsrc, -⟩ := hpost p t tmp x rfl hBP
    exact ⟨σ', by rw [hr], hs, hsrc, hC⟩
  | exc e σ' => simp only [wi32Spec, Spec.of] at hpost
  | wrong msg => simp only [wi32Spec, Spec.of] at hpost

/-! ## `writeI64(long)` -/

abbrev wi64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol».«writeI64(long)».ref

/-- What `writeI64(n)` guarantees: it appends the eight bytes of `n`, big-endian. -/
def wi64N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] → BPAt P R σ p t tmp →
    r = none ∧ BPAt P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.be 8 n.toNat ∧
    R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

attribute [irreducible] wi64N

def wi64Spec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] ∧ BPAt P R σ p t tmp)
  (wi64N P R)
  (fun _ _ _ _ => False)

def wi64SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I64), args = [.ref p, .long n] ∧ BPAt P R σ p t tmp ∧
     BPAtH P R σ p t tmp)
  (wi64N P R)
  (fun _ _ _ _ => False)

/-- Statement 49 (the load of `trans_`): the eight bytes are in `inoutTemp`. -/
def wi64Inv : Invariants := [(49, fun args σ0 fr σ =>
  ∀ (p tmp : Addr) (n0 : I64) (fs : List (FieldKey × Value)), args = [.ref p, .long n0] →
  σ0.heap p = some (.plain bpCls fs) → Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) →
  ∃ (xs : List Value), fr.get 6 = some (.ref p) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    (xs.take 8).map byteOf = Spec.be 8 n0.toNat ∧
    σ.next = σ0.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    (∀ a, a ≠ tmp → σ.heap a = σ0.heap a))]

theorem wi64_bytes (n : I64) :
    [byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 56#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 48#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 40#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 32#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 24#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 16#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& JLong.shr n 8#32))))),
      byteOf (.int (JInt.toByte (JInt.toByte (JLong.toInt (255#64 &&& n)))))] = Spec.be 8 n.toNat := by
  simp only [byteOf_mask255L]
  rw [Spec.be_eight, ofNat_shrL n 56 (by decide), ofNat_shrL n 48 (by decide), ofNat_shrL n 40 (by decide),
    ofNat_shrL n 32 (by decide), ofNat_shrL n 24 (by decide), ofNat_shrL n 16 (by decide),
    ofNat_shrL n 8 (by decide)]

theorem wi64_exit_post {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp : Addr} {n0 : I64}
    {xs : List Value}
    (hBP : BPAt P R σ0 p t tmp) (hheap : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ.next = σ0.next) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (htmpσ : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (hbytes : List.map byteOf (List.take 8 xs) = Spec.be 8 n0.toNat) (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t ++
      List.take (BitVec.ofNat 32 8).toNat (List.drop (0#32).toNat (List.map byteOf xs)))
    (hsrc : R.src σ' t = R.src σ t) (hf : TFrame R σ σ' t t) :
    wi64N P R [.ref p, .long n0] σ0 none σ' := by
  unfold wi64N
  intro p' t' tmp' n' he hBP'
  simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨rfl, rfl⟩ := bpAt_uniq hBP' hBP
  obtain ⟨h1, h2, h3, h4⟩ :=
    bw_exit_core hBP hheap hnext hin hst htmpσ hlen (by decide) hbytes hinv' hsink hsrc hf
  exact ⟨rfl, h1, h2, h3, h4⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi64_body (R : TRep) : BodyVCP (Contains · [bpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    wi64Ref (fun P => wi64SpecI P R) wi64Inv 80 := by
  jverify_body [Contains, tContracts, BPAt, PFrame, wi64SpecI, wi64Inv, writeSpec, writeSig, ttCls,
    bpCls, tpCls]
  case left.left => exact wi64_bytes _
  case right.some.some.true.left => exact bw_exit_pre R ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (by decide)
  case right.some.some.true.right.normal =>
    exact wi64_exit_post (BPAtH.elim ‹BPAtH _ R _ _ _ _›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (by unfold TFrame; exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩)

theorem wi64_sat (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wi64Ref (wi64Spec P R) := by
  have hI := BodyVCP.sat (wi64_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩ hm

theorem bw_toU64_toInt (x : I64) : Spec.toU 64 x.toInt = x.toNat := by
  have hx := x.isLt
  have h1 : x.toInt % (18446744073709551616 : Int) = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  show (x.toInt % ((2 ^ 64 : Nat) : Int)).toNat = _
  rw [show ((2 ^ 64 : Nat) : Int) = 18446744073709551616 from rfl, h1, Int.toNat_natCast]

/-- **E for binary i64**: in every program that contains the protocol classes and whose transport
classes satisfy the transport contracts, `writeI64(x)` returns normally after appending
`Spec.beI64 x` (the eight bytes of `x`, big-endian). -/
theorem wi64_E {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) {σ : State} {p t tmp : Addr} (hBP : BPAt P R σ p t tmp)
    (x : I64) {o : Outcome} (hm : MExec P wi64Ref [.ref p, .long x] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI64 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp := by
  have hpost := wi64_sat R hF hV [.ref p, .long x] σ o ⟨p, t, tmp, x, rfl, hBP⟩ hm
  rw [Spec.beI64, bw_toU64_toInt]
  cases o with
  | normal r σ' =>
    simp only [wi64Spec, Spec.of] at hpost
    unfold wi64N at hpost
    obtain ⟨hr, hC, hs, hsrc, -⟩ := hpost p t tmp x rfl hBP
    exact ⟨σ', by rw [hr], hs, hsrc, hC⟩
  | exc e σ' => simp only [wi64Spec, Spec.of] at hpost
  | wrong msg => simp only [wi64Spec, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
