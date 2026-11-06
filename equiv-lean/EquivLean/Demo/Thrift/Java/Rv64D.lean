import EquivLean.Demo.Thrift.Java.Rv32C

/-!
# Thrift → Java (T4): `TCompactProtocol.readVarint64()`, the contract and the loop invariants

As `readVarint32()` with 10 bytes and a `long`: the fast path needs 10 bytes in the buffer.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rv64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readVarint64()».ref

/-- What `readVarint64()` returns: the value of the varint (at most 10 bytes) mod `2^64`; the bytes
after it are left. -/
def rv64N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    ∃ v rest, Spec.readVarint 10 (R.src σ t) = some (v, rest) ∧ r = some (.long (BitVec.ofNat 64 v)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp

/-- When `readVarint64()` throws: more than 10 bytes (`TProtocolException`) or the input ends inside
the varint (`TTransportException`). -/
def rv64E (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    (Spec.VarintOverlong 10 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
    (Spec.VarintTruncated 10 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] rv64N rv64E

/-- The contract with hidden copies of the protocol facts, for the proof. -/
def rv64SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧
     ClassOK P σ t ∧ σ.initOf tpeCls = .done)
  (rv64N P R) (rv64E P R)

/-- The fast loop's facts about the buffer (10 bytes or more). -/
def FastFacts10 (R : TRep) (σ0 : State) (t : Addr) (arr : List Value) (i : Nat) (u : UInt8) : Prop :=
  10 ≤ R.bufLen σ0 t ∧ R.bufPos σ0 t + (R.bufLen σ0 t).toNat ≤ arr.length ∧
  (arr.drop (R.bufPos σ0 t)).take (R.bufLen σ0 t).toNat =
    ((R.src σ0 t).take (R.bufLen σ0 t).toNat).map jbyte ∧
  (R.bufLen σ0 t).toNat ≤ (R.src σ0 t).length ∧ R.bufPos σ0 t + (R.bufLen σ0 t).toNat < 2147483648 ∧
  (∀ c ∈ (R.src σ0 t).take i, 128 ≤ c.toNat) ∧ (R.src σ0 t)[i]? = some u

attribute [irreducible] FastFacts10

/-- The loops' heads. Statement 13 (fast loop): `i` groups read from the buffer, the next byte is
`u`. Statement 35 (slow loop): `k` bytes read with `readByte()`. -/
def rv64Inv (R : TRep) : Invariants :=
  [(13, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∃ (i : Nat) (arr : List Value) (u : UInt8), σ = σ0 ∧ i ≤ 9 ∧ fr.get 12 = some (.ref p) ∧
      fr.get 0 = some (.ref (R.bufArr σ0 t)) ∧
      fr.get 10 = some (.int (BitVec.ofNat 32 (R.bufPos σ0 t))) ∧
      fr.get 7 = some (.int (BitVec.ofNat 32 i)) ∧ fr.get 9 = some (.int (BitVec.ofNat 32 (7 * i))) ∧
      fr.get 2 = some (.long (BitVec.ofNat 64 (acc32 (R.src σ0 t) i))) ∧
      σ0.heap (R.bufArr σ0 t) = some (.array (.prim .byte) arr) ∧
      R.bufPos σ0 t + i < arr.length ∧ R.bufPos σ0 t + 9 < 2147483648 ∧
      arr[R.bufPos σ0 t + i]? = some (jbyte u) ∧
      (∃ h : R.bufPos σ0 t + i < arr.length, arr[R.bufPos σ0 t + i]'h = jbyte u) ∧
      FastFacts10 R σ0 t arr i u),
   (35, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∀ (c : ClassName) (fst0 : List (FieldKey × Value)), σ0.heap t = some (.plain c fst0) →
    ∃ (k : Nat) (fst : List (FieldKey × Value)), k ≤ 10 ∧ fr.get 12 = some (.ref p) ∧
      fr.get 9 = some (.int (BitVec.ofNat 32 k)) ∧
      fr.get 11 = some (.int (BitVec.ofNat 32 (7 * k))) ∧
      fr.get 1 = some (.long (BitVec.ofNat 64 (acc32 (R.src σ0 t) k))) ∧
      SlowFacts R σ0 σ t k ∧ CPAtR R σ p t tmp ∧ CPAtRH R σ p t tmp ∧
      σ.heap t = some (.plain c fst) ∧ PFrame R σ0 σ t tmp ∧
      (∀ a, a < σ0.next → ¬ R.owns σ0 t a → ¬ R.owns σ t a))]

end EquivLean.Demo.Thrift.Java
