import EquivLean.Demo.Thrift.Java.Bits

/-!
# Thrift → Java (T4): the transport contract

The protocols call their `TTransport` virtually (`write`, `readAll`, and the buffer fast path
`getBytesRemainingInBuffer`, `getBuffer`, `getBufferPosition`, `consumeBuffer`), and
`checkReadBytesAvailable`. The contract states these calls on an abstract representation `TRep`:
what the transport object has written (`sink`), what it still has to read (`src`), and its buffer
(`bufArr`, `bufPos`, `bufLen`: `bufLen` bytes of `src` at `bufPos` in the array `bufArr`). The
theorems hold in every program whose transport classes satisfy these contracts.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev Bytes := List UInt8

/-- A fact kept folded (the symbolic execution leaves it alone). -/
@[irreducible] def Hide (p : Prop) : Prop := p

theorem Hide.intro {p : Prop} (h : p) : Hide p := by unfold Hide; exact h
theorem Hide.elim {p : Prop} (h : Hide p) : p := by unfold Hide at h; exact h

/-- The byte a Java `byte` array element holds (its low 8 bits). -/
def byteOf : Value → UInt8
  | .int v => UInt8.ofNat v.toNat
  | _ => 0

/-- The Java `byte` (sign-extended) of `b`. -/
def jbyte (b : UInt8) : Value := .int (BitVec.signExtend 32 b.toBitVec)

def ttCls : ClassName := "org.apache.thrift.transport.TTransport"
def ttExcCls : ClassName := "org.apache.thrift.transport.TTransportException"

/-- **The representation of a transport object** and its laws. -/
structure TRep where
  /-- The objects the transport object `t` uses (its buffers, streams). -/
  owns : State → Addr → Addr → Prop
  /-- The bytes written to `t` so far. -/
  sink : State → Addr → Bytes
  /-- The bytes `t` still has to read. -/
  src : State → Addr → Bytes
  /-- The fast-path buffer: array, position, number of bytes of `src` there (`≤ 0`: none). -/
  bufArr : State → Addr → Addr
  bufPos : State → Addr → Nat
  bufLen : State → Addr → Int
  /-- `t` is a working transport. -/
  inv : State → Addr → Prop
  inv_owns : ∀ σ t a, inv σ t → owns σ t a → a < σ.next ∧ a ≠ t
  /-- The representation depends only on `t` and the objects it uses. -/
  local_ : ∀ σ σ' t, inv σ t → σ'.heap t = σ.heap t → (∀ a, owns σ t a → σ'.heap a = σ.heap a) →
    σ.next ≤ σ'.next →
    inv σ' t ∧ sink σ' t = sink σ t ∧ src σ' t = src σ t ∧ bufArr σ' t = bufArr σ t ∧
      bufPos σ' t = bufPos σ t ∧ bufLen σ' t = bufLen σ t ∧ (∀ a, owns σ' t a ↔ owns σ t a)
  /-- The buffer holds the next `bufLen` bytes of `src`, as Java bytes. -/
  inv_buf : ∀ σ t, inv σ t → 0 < bufLen σ t →
    ∃ arr, σ.heap (bufArr σ t) = some (.array (.prim .byte) arr) ∧ owns σ t (bufArr σ t) ∧
      bufPos σ t + (bufLen σ t).toNat ≤ arr.length ∧
      (arr.drop (bufPos σ t)).take (bufLen σ t).toNat = ((src σ t).take (bufLen σ t).toNat).map jbyte ∧
      (bufLen σ t).toNat ≤ (src σ t).length ∧ bufPos σ t + (bufLen σ t).toNat < 2147483648
  inv_len : ∀ σ t, inv σ t → -2147483648 ≤ bufLen σ t ∧ bufLen σ t < 2147483648

/-- A transport call changed only `t`, the objects it uses and `x` (`x = t`: no other object);
`t` keeps its class and does not take over other objects. -/
def TFrame (R : TRep) (σ σ' : State) (t x : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
  (∀ a, a < σ.next → a ≠ t → ¬ R.owns σ t a → a ≠ x → σ'.heap a = σ.heap a) ∧
  (∀ a, a < σ.next → ¬ R.owns σ t a → ¬ R.owns σ' t a) ∧
  (∀ c fs, σ.heap t = some (.plain c fs) → ∃ fs', σ'.heap t = some (.plain c fs'))

def writeSig : MethodSig := ⟨ttCls, .void, "write", [.array (.prim .byte), .prim .int, .prim .int]⟩
def readAllSig : MethodSig := ⟨ttCls, .prim .int, "readAll", [.array (.prim .byte), .prim .int, .prim .int]⟩
def getBufferSig : MethodSig := ⟨ttCls, .array (.prim .byte), "getBuffer", []⟩
def getBufferPositionSig : MethodSig := ⟨ttCls, .prim .int, "getBufferPosition", []⟩
def getBytesRemainingInBufferSig : MethodSig := ⟨ttCls, .prim .int, "getBytesRemainingInBuffer", []⟩
def consumeBufferSig : MethodSig := ⟨ttCls, .void, "consumeBuffer", [.prim .int]⟩
def checkReadBytesAvailableSig : MethodSig := ⟨ttCls, .void, "checkReadBytesAvailable", [.prim .long]⟩

/-- `write(buf, off, len)` appends `buf[off, off + len)` to the sink. -/
def writeSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (t buf : Addr) (off len : I32) (arr : List Value), args = [.ref t, .ref buf, .int off, .int len] ∧
     R.inv σ t ∧ σ.heap buf = some (.array (.prim .byte) arr) ∧ 0 ≤ off.toInt ∧ 0 ≤ len.toInt ∧
     off.toInt + len.toInt ≤ arr.length ∧ buf ≠ t ∧ ¬ R.owns σ t buf)
  (fun args σ r σ' => ∀ (t buf : Addr) (off len : I32) (arr : List Value), args = [.ref t, .ref buf, .int off, .int len] →
     σ.heap buf = some (.array (.prim .byte) arr) →
     r = none ∧ R.inv σ' t ∧
     R.sink σ' t = R.sink σ t ++ ((arr.drop off.toNat).take len.toNat).map byteOf ∧
     R.src σ' t = R.src σ t ∧ TFrame R σ σ' t t)
  (fun _ _ _ _ => False)

/-- `readAll(buf, off, len)` fills `buf[off, off + len)` with the next `len` bytes, or throws a
`TTransportException` when fewer are left. -/
def readAllSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (t buf : Addr) (off len : I32) (arr : List Value), args = [.ref t, .ref buf, .int off, .int len] ∧
     R.inv σ t ∧ σ.heap buf = some (.array (.prim .byte) arr) ∧ 0 ≤ off.toInt ∧ 0 ≤ len.toInt ∧
     off.toInt + len.toInt ≤ arr.length ∧ buf ≠ t ∧ ¬ R.owns σ t buf)
  (fun args σ r σ' => ∀ (t buf : Addr) (off len : I32) (arr : List Value), args = [.ref t, .ref buf, .int off, .int len] →
     σ.heap buf = some (.array (.prim .byte) arr) →
     r = some (.int len) ∧ len.toNat ≤ (R.src σ t).length ∧ R.inv σ' t ∧
     σ'.heap buf = some (.array (.prim .byte)
       (arr.take off.toNat ++ ((R.src σ t).take len.toNat).map jbyte ++
         arr.drop (off.toNat + len.toNat))) ∧
     R.src σ' t = (R.src σ t).drop len.toNat ∧ R.sink σ' t = R.sink σ t ∧ TFrame R σ σ' t buf)
  (fun args σ e σ' => ∀ (t buf : Addr) (off len : I32) (arr : List Value), args = [.ref t, .ref buf, .int off, .int len] →
     σ.heap buf = some (.array (.prim .byte) arr) →
     (R.src σ t).length < len.toNat ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs)) ∧
     TFrame R σ σ' t buf)

/-- The buffer holds the next `bufLen` bytes of the source, at `bufPos` in `bufArr` (Java bytes);
in particular (the buffer is not empty) the next byte `u` is at `bufPos`. -/
def BufView (R : TRep) (σ : State) (t : Addr) : Prop :=
  ∃ arr, σ.heap (R.bufArr σ t) = some (.array (.prim .byte) arr) ∧
    R.bufPos σ t + (R.bufLen σ t).toNat ≤ arr.length ∧
    (arr.drop (R.bufPos σ t)).take (R.bufLen σ t).toNat =
      ((R.src σ t).take (R.bufLen σ t).toNat).map jbyte ∧
    (R.bufLen σ t).toNat ≤ (R.src σ t).length ∧ R.bufPos σ t + (R.bufLen σ t).toNat < 2147483648 ∧
    ∃ u rest, R.src σ t = u :: rest ∧ arr[R.bufPos σ t]? = some (jbyte u) ∧
      ∃ h : R.bufPos σ t < arr.length, arr[R.bufPos σ t]'h = jbyte u

/-- `getBytesRemainingInBuffer()` returns `bufLen` and changes nothing. -/
def getBytesRemainingInBufferSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ t, args = [.ref t] ∧ R.inv σ t)
  (fun args σ r σ' => ∀ t, args = [.ref t] →
     r = some (.int (BitVec.ofInt 32 (R.bufLen σ t))) ∧ σ' = σ ∧
     -2147483648 ≤ R.bufLen σ t ∧ R.bufLen σ t < 2147483648)
  (fun _ _ _ _ => False)

/-- `getBuffer()` returns the buffer array (when the buffer is not empty). -/
def getBufferSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ t, args = [.ref t] ∧ R.inv σ t ∧ 0 < R.bufLen σ t)
  (fun args σ r σ' => ∀ t, args = [.ref t] → r = some (.ref (R.bufArr σ t)) ∧ σ' = σ ∧ BufView R σ t)
  (fun _ _ _ _ => False)

/-- `getBufferPosition()` returns the buffer position (when the buffer is not empty). -/
def getBufferPositionSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ t, args = [.ref t] ∧ R.inv σ t ∧ 0 < R.bufLen σ t)
  (fun args σ r σ' => ∀ t, args = [.ref t] →
     r = some (.int (BitVec.ofNat 32 (R.bufPos σ t))) ∧ σ' = σ ∧
     R.bufPos σ t + (R.bufLen σ t).toNat < 2147483648)
  (fun _ _ _ _ => False)

/-- `consumeBuffer(n)` drops `n` bytes of the buffer from the source; only `t` itself changes. -/
def consumeBufferSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (t : Addr) (n : I32), args = [.ref t, .int n] ∧ R.inv σ t ∧ 0 ≤ n.toInt ∧
     n.toInt ≤ R.bufLen σ t)
  (fun args σ r σ' => ∀ (t : Addr) (n : I32), args = [.ref t, .int n] →
     r = none ∧ R.inv σ' t ∧ R.src σ' t = (R.src σ t).drop n.toNat ∧ R.sink σ' t = R.sink σ t ∧
     R.bufArr σ' t = R.bufArr σ t ∧ R.bufPos σ' t = R.bufPos σ t + n.toNat ∧
     R.bufLen σ' t = R.bufLen σ t - n.toInt ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
     σ'.statics = σ.statics ∧ (∀ a, a ≠ t → σ'.heap a = σ.heap a) ∧
     (∀ a, R.owns σ' t a ↔ R.owns σ t a) ∧
     (∀ c fs, σ.heap t = some (.plain c fs) → ∃ fs', σ'.heap t = some (.plain c fs')))
  (fun _ _ _ _ => False)

/-- `checkReadBytesAvailable(n)` returns and changes nothing (no message-size limit). -/
def checkReadBytesAvailableSpec (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (t : Addr) (n : I64), args = [.ref t, .long n] ∧ R.inv σ t)
  (fun args σ r σ' => ∀ (t : Addr) (n : I64), args = [.ref t, .long n] → r = none ∧ σ' = σ)
  (fun _ _ _ _ => False)

/-- **The transport contracts.** -/
def tContracts (R : TRep) : Contracts :=
  [(writeSig, writeSpec R), (readAllSig, readAllSpec R),
   (getBytesRemainingInBufferSig, getBytesRemainingInBufferSpec R), (getBufferSig, getBufferSpec R),
   (getBufferPositionSig, getBufferPositionSpec R), (consumeBufferSig, consumeBufferSpec R),
   (checkReadBytesAvailableSig, checkReadBytesAvailableSpec R)]

/-! ## The laws at work: updates and allocations of other objects -/

namespace TRep

/-- An update of an object that `t` does not use leaves the representation of `t`. -/
theorem setObj_eq (R : TRep) {σ : State} {t a : Addr} {o : Obj} (h : R.inv σ t) (ha : a ≠ t)
    (ho : ¬ R.owns σ t a) :
    R.inv (σ.setObj a o) t ∧ R.sink (σ.setObj a o) t = R.sink σ t ∧
      R.src (σ.setObj a o) t = R.src σ t ∧ R.bufArr (σ.setObj a o) t = R.bufArr σ t ∧
      R.bufPos (σ.setObj a o) t = R.bufPos σ t ∧ R.bufLen (σ.setObj a o) t = R.bufLen σ t ∧
      (∀ b, R.owns (σ.setObj a o) t b ↔ R.owns σ t b) := by
  apply R.local_ σ _ t h
  · rw [State.heap_setObj, if_neg (Ne.symm ha)]
  · intro b hb
    have hba : b ≠ a := fun e => ho (e ▸ hb)
    rw [State.heap_setObj, if_neg hba]
  · rw [State.next_setObj]
    exact Nat.le_refl _

/-- An allocation leaves the representation of `t`. -/
theorem alloc_eq (R : TRep) {σ : State} {t : Addr} {o : Obj} (h : R.inv σ t) (ht : t < σ.next) :
    R.inv (σ.alloc o).2 t ∧ R.sink (σ.alloc o).2 t = R.sink σ t ∧
      R.src (σ.alloc o).2 t = R.src σ t ∧ R.bufArr (σ.alloc o).2 t = R.bufArr σ t ∧
      R.bufPos (σ.alloc o).2 t = R.bufPos σ t ∧ R.bufLen (σ.alloc o).2 t = R.bufLen σ t ∧
      (∀ b, R.owns (σ.alloc o).2 t b ↔ R.owns σ t b) := by
  apply R.local_ σ _ t h
  · exact State.heap_alloc_of_lt ht o
  · intro b hb
    exact State.heap_alloc_of_lt (R.inv_owns σ t b h hb).1 o
  · rw [State.next_alloc]
    exact Nat.le_succ _

end TRep

theorem byteOf_toByte (w : I32) : byteOf (.int (JInt.toByte w)) = UInt8.ofNat w.toNat := by
  simp only [byteOf]
  apply UInt8.toBitVec_inj.mp
  show BitVec.ofNat 8 _ = BitVec.ofNat 8 _
  rw [BitVec.ofNat_toNat, BitVec.ofNat_toNat, toByte_setWidth8]

theorem byteOf_jbyte (b : UInt8) : byteOf (jbyte b) = b := by
  simp only [byteOf, jbyte]
  apply UInt8.toBitVec_inj.mp
  show BitVec.ofNat 8 _ = _
  rw [BitVec.ofNat_toNat, setWidth8_signExtend32]

end EquivLean.Demo.Thrift.Java
