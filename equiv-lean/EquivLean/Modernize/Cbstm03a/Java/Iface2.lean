import EquivLean.Modernize.Cbstm03a.Java.Iface0

/-!
# CBSTM03A → Java: the table memory (contracts)

COBOL's `WS-TRNX-TABLE` (`CARD_MAX = 51` cards of `CARD_SZ = 3356` characters: a 16-character card number, then 10
entries of `TRAN_SZ = 334`) is emulated by an array of `51 * 11` string slots (slot `11 c` the card number of card
`c`, slot `11 c + k` its entry `k`, `1 ≤ k ≤ 10`), written lazily: a `null` slot stands for spaces. The abstract
view is the memory `m : Nat → JChar`, related to the slots array by `SlotsAt σ a m` (positions `0 ≤ j < MEM_SZ =
171156`; `m` is unconstrained at other positions). `memWrite(slots, off, s)` writes `s` (of `int` length) at
`off` (any `long`), dropping the characters that fall outside `[0, MEM_SZ)` (`memWr`); `memRead(slots, off, n)`
reads `n` characters at `off`, spaces outside `[0, MEM_SZ)` (`memRd`; for `off > -2^31`: below that the Java
loop can return a wrong text, e.g. `""` for `off = -6442450944`, `n = 16`). `trct` (`long[51]`): `setTrct`/`getTrct`
at `cr - 1` for `1 ≤ cr ≤ 51`, dropped/`0` otherwise. `seqRead(texts, st)`, `st = {index, eof}`: `"46"` after
the end, `"00"` (index + 1) while records remain, `"10"` (eof set) at the end.

Conventions of `CbA.Iface0`: methods that allocate nothing: `σ' = σ`; a string result is a new object
(`σ.next ≤ x`), with `Grows σ σ'`; a method that updates an object in place (`memWrite`: the slots array; `setTrct`:
`trct`; `seqRead`: `st`) describes the object in `σ'` and keeps every other object of `σ`
(`Keeps (· = a) σ σ'`); `inits`/`statics` unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## Slot geometry and the memory -/

/-- The slot holding memory position `o < MEM_SZ`: `11 × card + entry` (entry 0: the card number). -/
def slotIdx (o : Nat) : Nat := o / 3356 * 11 + if o % 3356 < 16 then 0 else 1 + (o % 3356 - 16) / 334

/-- The first memory position of slot `i`. -/
def slotSt (i : Nat) : Nat := i / 11 * 3356 + if i % 11 = 0 then 0 else 16 + (i % 11 - 1) * 334

/-- The length of slot `i`: 16 (a card number) or 334 (an entry). -/
def slotLn (i : Nat) : Nat := if i % 11 = 0 then 16 else 334

/-- The slots array at `a` holds the memory `m`: an array of 561 strings or `null`s; a non-null slot `i` is a string
of `slotLn i` characters, the memory at positions `slotSt i + w`; a `null` slot `i` stands for spaces there. -/
def SlotsAt (σ : State) (a : Addr) (m : Nat → JChar) : Prop :=
  ∃ vs, σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ vs.length = 561 ∧
    ∀ i, i < 561 →
      (vs[i]? = some .null ∧ ∀ w, w < slotLn i → m (slotSt i + w) = space) ∨
      (∃ x t, vs[i]? = some (.ref x) ∧ σ.heap x = some (.str t) ∧ t.length = slotLn i ∧
        ∀ w, w < slotLn i → m (slotSt i + w) = t.getD w space)

/-- `s` written at offset `off`: the characters falling outside `[0, MEM_SZ)` are dropped. -/
def memWr (m : Nat → JChar) (off : Int) (s : JStr) : Nat → JChar := fun j =>
  if j < 171156 ∧ off ≤ (j : Int) ∧ (j : Int) < off + s.length then s.getD (j - off).toNat space else m j

/-- The `n` characters at offset `off`: spaces outside `[0, MEM_SZ)`. -/
def memRd (m : Nat → JChar) (off : Int) (n : Nat) : JStr :=
  (List.range n).map fun i => if 0 ≤ off + i ∧ off + i < 171156 then m (off + i).toNat else space

/-- `trct` after `setTrct(trct, cr, v)`. -/
def trctSet (vs : List Value) (cr v : I64) : List Value :=
  if 1 ≤ cr.toInt ∧ cr.toInt ≤ 51 then vs.set (cr.toInt - 1).toNat (.long v) else vs

/-- `getTrct(trct, cr)`. -/
def trctGet (vs : List Value) (cr : I64) : Value :=
  if 1 ≤ cr.toInt ∧ cr.toInt ≤ 51 then vs.getD (cr.toInt - 1).toNat (.long 0) else .long 0

/-- The status `seqRead` returns for `st = {i, e}` and `len` records: `"46"` once the end was seen, `"00"` while
records remain, `"10"` at the end. -/
def seqCode (i e : I32) (len : Nat) : JStr :=
  if e ≠ 0 then JStr.ofString "46" else if i.toInt < len then JStr.ofString "00" else JStr.ofString "10"

/-- `st` after `seqRead`. -/
def seqStArr (i e : I32) (len : Nat) : List Value :=
  if e ≠ 0 then [.int i, .int e] else if i.toInt < len then [.int (i + 1), .int e] else [.int i, .int 1]

/-! ## The methods -/

abbrev cardOffRef : MethodRef := Gen.Cbstm03a.«cardOff(long)».ref
abbrev tranOffRef : MethodRef := Gen.Cbstm03a.«tranOff(long,long)».ref
abbrev slotIndexRef : MethodRef := Gen.Cbstm03a.«slotIndex(long)».ref
abbrev slotStartRef : MethodRef := Gen.Cbstm03a.«slotStart(int)».ref
abbrev slotLenRef : MethodRef := Gen.Cbstm03a.«slotLen(int)».ref
abbrev memWriteRef : MethodRef := Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)».ref
abbrev memReadRef : MethodRef := Gen.Cbstm03a.«memRead(java.lang.String[],long,int)».ref
abbrev setTrctRef : MethodRef := Gen.Cbstm03a.«setTrct(long[],long,long)».ref
abbrev getTrctRef : MethodRef := Gen.Cbstm03a.«getTrct(long[],long)».ref
abbrev seqReadRef : MethodRef := Gen.Cbstm03a.«seqRead(java.lang.String[],int[])».ref

def cardOffSig : MethodSig := ⟨"Cbstm03a", .prim .long, "cardOff", [.prim .long]⟩
def tranOffSig : MethodSig := ⟨"Cbstm03a", .prim .long, "tranOff", [.prim .long, .prim .long]⟩
def slotIndexSig : MethodSig := ⟨"Cbstm03a", .prim .int, "slotIndex", [.prim .long]⟩
def slotStartSig : MethodSig := ⟨"Cbstm03a", .prim .long, "slotStart", [.prim .int]⟩
def slotLenSig : MethodSig := ⟨"Cbstm03a", .prim .int, "slotLen", [.prim .int]⟩
def memWriteSig : MethodSig :=
  ⟨"Cbstm03a", .void, "memWrite", [.array (.cls "java.lang.String"), .prim .long, .cls "java.lang.String"]⟩
def memReadSig : MethodSig :=
  ⟨"Cbstm03a", .cls "java.lang.String", "memRead", [.array (.cls "java.lang.String"), .prim .long, .prim .int]⟩
def setTrctSig : MethodSig := ⟨"Cbstm03a", .void, "setTrct", [.array (.prim .long), .prim .long, .prim .long]⟩
def getTrctSig : MethodSig := ⟨"Cbstm03a", .prim .long, "getTrct", [.array (.prim .long), .prim .long]⟩
def seqReadSig : MethodSig :=
  ⟨"Cbstm03a", .cls "java.lang.String", "seqRead", [.array (.cls "java.lang.String"), .array (.prim .int)]⟩

/-- `cardOff(cr)`: `(cr - 1) × CARD_SZ` (64-bit arithmetic). -/
def cardOffSpec : Spec := Spec.of
  (fun args _ => ∃ cr : I64, args = [.long cr])
  (fun args σ r σ' => ∀ cr : I64, args = [.long cr] → r = some (.long ((cr - 1) * 3356)) ∧ σ' = σ)

/-- `tranOff(cr, tr)`: `(cr - 1) × CARD_SZ + 16 + (tr - 1) × TRAN_SZ` (64-bit arithmetic). -/
def tranOffSpec : Spec := Spec.of
  (fun args _ => ∃ cr tr : I64, args = [.long cr, .long tr])
  (fun args σ r σ' => ∀ cr tr : I64, args = [.long cr, .long tr] →
     r = some (.long ((cr - 1) * 3356 + 16 + (tr - 1) * 334)) ∧ σ' = σ)

/-- `slotIndex(o)`, `0 ≤ o < MEM_SZ`: the slot holding position `o`. -/
def slotIndexSpec : Spec := Spec.of
  (fun args _ => ∃ o : I64, args = [.long o] ∧ 0 ≤ o.toInt ∧ o.toInt < 171156)
  (fun args σ r σ' => ∀ o : I64, args = [.long o] →
     r = some (.int (BitVec.ofNat 32 (slotIdx o.toNat))) ∧ σ' = σ)

/-- `slotStart(i)`, `0 ≤ i`: the first position of slot `i`. -/
def slotStartSpec : Spec := Spec.of
  (fun args _ => ∃ i : I32, args = [.int i] ∧ 0 ≤ i.toInt)
  (fun args σ r σ' => ∀ i : I32, args = [.int i] →
     r = some (.long (BitVec.ofNat 64 (slotSt i.toNat))) ∧ σ' = σ)

/-- `slotLen(i)`, `0 ≤ i`: the length of slot `i`. -/
def slotLenSpec : Spec := Spec.of
  (fun args _ => ∃ i : I32, args = [.int i] ∧ 0 ≤ i.toInt)
  (fun args σ r σ' => ∀ i : I32, args = [.int i] →
     r = some (.int (BitVec.ofNat 32 (slotLn i.toNat))) ∧ σ' = σ)

/-- `memWrite(slots, off, s)`, `off > -2^31`, `Cbstm03a` initialized: the slots array holds `memWr m off s`; every
other object is unchanged. -/
def memWriteSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (off : I64) (x : Addr) (m : Nat → JChar) (t : JStr),
     args = [.ref a, .long off, .ref x] ∧ SlotsAt σ a m ∧
     σ.heap x = some (.str t) ∧ t.length < 2147483648 ∧ -2147483648 < off.toInt ∧
     σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (a : Addr) (off : I64) (x : Addr) (m : Nat → JChar) (t : JStr),
     args = [.ref a, .long off, .ref x] → SlotsAt σ a m →
     σ.heap x = some (.str t) →
     r = none ∧ SlotsAt σ' a (memWr m off.toInt t) ∧ Keeps (· = a) σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `memRead(slots, off, n)`, `off > -2^31`, `n ≤ 2^30`, `Cbstm03a` initialized: a new string, the `n` characters
(none for `n ≤ 0`) at `off`. -/
def memReadSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (off : I64) (n : I32) (m : Nat → JChar),
     args = [.ref a, .long off, .int n] ∧ SlotsAt σ a m ∧
     -2147483648 < off.toInt ∧ n.toInt ≤ 1073741824 ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (a : Addr) (off : I64) (n : I32) (m : Nat → JChar),
     args = [.ref a, .long off, .int n] → SlotsAt σ a m →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (memRd m off.toInt n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `setTrct(trct, cr, v)`, `trct` a `long[]` of at least 51 elements. -/
def setTrctSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (cr v : I64) (vs : List Value), args = [.ref a, .long cr, .long v] ∧
     σ.heap a = some (.array (.prim .long) vs) ∧ 51 ≤ vs.length)
  (fun args σ r σ' => ∀ (a : Addr) (cr v : I64) (vs : List Value), args = [.ref a, .long cr, .long v] →
     σ.heap a = some (.array (.prim .long) vs) →
     r = none ∧ σ'.heap a = some (.array (.prim .long) (trctSet vs cr v)) ∧ Keeps (· = a) σ σ' ∧
       σ'.next = σ.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `getTrct(trct, cr)`, `trct` a `long[]` of at least 51 elements. -/
def getTrctSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (cr : I64) (vs : List Value), args = [.ref a, .long cr] ∧
     σ.heap a = some (.array (.prim .long) vs) ∧ 51 ≤ vs.length)
  (fun args σ r σ' => ∀ (a : Addr) (cr : I64) (vs : List Value), args = [.ref a, .long cr] →
     σ.heap a = some (.array (.prim .long) vs) → r = some (trctGet vs cr) ∧ σ' = σ)

/-- `seqRead(texts, st)`, `st = {i, e}` an `int[2]`: a new status string; `st` updated. -/
def seqReadSpec : Spec := Spec.of
  (fun args σ => ∃ (a b : Addr) (txs : List Value) (i e : I32), args = [.ref a, .ref b] ∧
     σ.heap a = some (.array (.cls "java.lang.String") txs) ∧ txs.length < 2147483648 ∧
     σ.heap b = some (.array (.prim .int) [.int i, .int e]))
  (fun args σ r σ' => ∀ (a b : Addr) (txs : List Value) (i e : I32), args = [.ref a, .ref b] →
     σ.heap a = some (.array (.cls "java.lang.String") txs) → txs.length < 2147483648 →
     σ.heap b = some (.array (.prim .int) [.int i, .int e]) →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (seqCode i e txs.length)) ∧
       σ'.heap b = some (.array (.prim .int) (seqStArr i e txs.length)) ∧ Keeps (· = b) σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The contracts of this part (for callers: `memContracts.env`). -/
def memContracts : Contracts :=
  [(cardOffSig, cardOffSpec), (tranOffSig, tranOffSpec), (slotIndexSig, slotIndexSpec),
   (slotStartSig, slotStartSpec), (slotLenSig, slotLenSpec), (memWriteSig, memWriteSpec),
   (memReadSig, memReadSpec), (setTrctSig, setTrctSpec), (getTrctSig, getTrctSpec), (seqReadSig, seqReadSpec)]

example : cardOffRef.sig = cardOffSig := rfl
example : tranOffRef.sig = tranOffSig := rfl
example : slotIndexRef.sig = slotIndexSig := rfl
example : slotStartRef.sig = slotStartSig := rfl
example : slotLenRef.sig = slotLenSig := rfl
example : memWriteRef.sig = memWriteSig := rfl
example : memReadRef.sig = memReadSig := rfl
example : setTrctRef.sig = setTrctSig := rfl
example : getTrctRef.sig = getTrctSig := rfl
example : seqReadRef.sig = seqReadSig := rfl

end EquivLean.Modernize.Cbstm03a.Java
