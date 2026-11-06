import EquivLean.Demo.Thrift.Java.Exc

/-!
# Thrift → Java (T4): `TCompactProtocol.readVarint32()` reads the varint (D, M)

The buffer fast path (at least 5 bytes in the buffer: the groups are read from `getBuffer()`, then
`consumeBuffer(n)`) or byte by byte with `readByte()`. At most 5 bytes: a fifth byte with the high
bit set throws a `TProtocolException`; the value is the groups ORed into an `int` (a fifth group
above bit 31 is lost, `v mod 2^32`); an input that ends inside the varint throws the transport's
`TTransportException`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rv32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readVarint32()».ref
abbrev twC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TWriteProtocol»
abbrev trC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TReadProtocol»

def tpeCls : ClassName := "org.apache.thrift.protocol.TProtocolException"

/-- What `readVarint32()` returns: the value of the varint (at most 5 bytes) mod `2^32`; the bytes
after it are left. -/
def rv32N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    ∃ v rest, Spec.readVarint 5 (R.src σ t) = some (v, rest) ∧ r = some (.int (BitVec.ofNat 32 v)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp ∧
      OwnsMono R σ σ' t

/-- When `readVarint32()` throws: more than 5 bytes (`TProtocolException`) or the input ends inside
the varint (`TTransportException`). -/
def rv32E (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    (Spec.VarintOverlong 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
    (Spec.VarintTruncated 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] rv32N rv32E

/-- The contract with hidden copies of the protocol facts, for the proof. -/
def rv32SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧
     ClassOK P σ t ∧ σ.initOf tpeCls = .done)
  (rv32N P R) (rv32E P R)

/-- The protocol object's facts without the program facts about the transport's class. -/
def CPAtR (R : TRep) (σ : State) (p t tmp : Addr) : Prop :=
  ∃ fs xs, σ.heap p = some (.plain cpCls fs) ∧
    Fields.get fs (tpCls, "trans_") = some (.ref t) ∧
    Fields.get fs (cpCls, "temp") = some (.ref tmp) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    R.inv σ t ∧ p ≠ t ∧ tmp ≠ t ∧ p ≠ tmp ∧ ¬ R.owns σ t p ∧ ¬ R.owns σ t tmp

/-- A folded copy of `CPAtR` (kept as a hypothesis through the symbolic execution). -/
def CPAtRH (R : TRep) (σ : State) (p t tmp : Addr) : Prop := CPAtR R σ p t tmp

attribute [irreducible] CPAtRH

/-- The loops' heads. Statement 13 (fast loop): `i` groups read from the buffer, the next byte is
`u`. Statement 35 (slow loop): `k` bytes read with `readByte()`. -/
def rv32Inv (R : TRep) : Invariants :=
  [(13, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∃ (i : Nat) (arr : List Value) (u : UInt8), σ = σ0 ∧ i ≤ 4 ∧ fr.get 13 = some (.ref p) ∧
      fr.get 0 = some (.ref (R.bufArr σ0 t)) ∧
      fr.get 8 = some (.int (BitVec.ofNat 32 (R.bufPos σ0 t))) ∧
      fr.get 9 = some (.int (BitVec.ofNat 32 i)) ∧ fr.get 6 = some (.int (BitVec.ofNat 32 (7 * i))) ∧
      fr.get 7 = some (.int (BitVec.ofNat 32 (acc32 (R.src σ0 t) i))) ∧
      σ0.heap (R.bufArr σ0 t) = some (.array (.prim .byte) arr) ∧
      R.bufPos σ0 t + i < arr.length ∧ R.bufPos σ0 t + 4 < 2147483648 ∧
      arr[R.bufPos σ0 t + i]? = some (jbyte u) ∧
      (∃ h : R.bufPos σ0 t + i < arr.length, arr[R.bufPos σ0 t + i]'h = jbyte u) ∧
      FastFacts R σ0 t arr i u),
   (35, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∀ (c : ClassName) (fst0 : List (FieldKey × Value)), σ0.heap t = some (.plain c fst0) →
    ∃ (k : Nat) (fst : List (FieldKey × Value)), k ≤ 5 ∧ fr.get 13 = some (.ref p) ∧
      fr.get 6 = some (.int (BitVec.ofNat 32 k)) ∧
      fr.get 10 = some (.int (BitVec.ofNat 32 (7 * k))) ∧
      fr.get 11 = some (.int (BitVec.ofNat 32 (acc32 (R.src σ0 t) k))) ∧
      SlowFacts R σ0 σ t k ∧ CPAtR R σ p t tmp ∧ CPAtRH R σ p t tmp ∧
      σ.heap t = some (.plain c fst) ∧ PFrame R σ0 σ t tmp ∧
      (∀ a, a < σ0.next → ¬ R.owns σ0 t a → ¬ R.owns σ t a))]

end EquivLean.Demo.Thrift.Java
