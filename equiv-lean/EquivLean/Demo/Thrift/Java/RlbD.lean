import EquivLean.Demo.Thrift.Java.FhR

/-!
# Thrift → Java (T4): the compact list/set header reader, definitions

`readListBegin()`: `size_and_type = readByte()`; `size = (size_and_type >> 4) & 0x0F`, or
`readVarint32()` when that is 15; `checkContainerReadLength(size)` (negative, or above
`containerLengthLimit_` unless that is `-1`: a `TProtocolException`); `new TList(getTType(
size_and_type), size)`; `checkReadBytesAvailable(list)` (`getMinSerializedSize(elemType)`, which
throws a `TTransportException` for a type code it does not list, then the transport's
`checkReadBytesAvailable`). `readSetBegin()` is `new TSet(readListBegin())`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev tlC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TList»
abbrev tsC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TSet»
abbrev tteC := EquivLean.Gen.ThriftJ.«org.apache.thrift.transport.TTransportException»

def tlCls : ClassName := "org.apache.thrift.protocol.TList"
def tsCls : ClassName := "org.apache.thrift.protocol.TSet"

/-! ## `checkContainerReadLength(int)` -/

abbrev ccrlRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«checkContainerReadLength(int)».ref

def ccrlSig : MethodSig := ⟨cpCls, .void, "checkContainerReadLength", [.prim .int]⟩

/-- Within the configured limit (`containerLengthLimit_ = -1`: no limit). -/
def InLimit (lim : I64) (size : I32) : Prop := lim = -1#64 ∨ size.toInt ≤ lim.toInt

/-- `checkContainerReadLength(n)` returns, changing nothing, for `n ≥ 0` within the limit (the
facts about the limit field stated last, so that a caller gets the result from the arguments). -/
def ccrlN (args : List Value) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∀ (p : Addr) (n : I32), args = [.ref p, .int n] → r = none ∧ σ' = σ ∧
    ∀ (fs : List (FieldKey × Value)) (lim : I64), σ.heap p = some (.plain cpCls fs) →
      Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) → 0 ≤ n.toInt ∧ InLimit lim n

/-- Otherwise it throws a `TProtocolException`. -/
def ccrlE (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p : Addr) (n : I32), args = [.ref p, .int n] → (∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∧
    ∀ (fs : List (FieldKey × Value)) (lim : I64), σ.heap p = some (.plain cpCls fs) →
      Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
        n.toInt < 0 ∨ ¬ InLimit lim n

attribute [irreducible] ccrlN ccrlE

def ccrlSpec : Spec := Spec.of
  (fun args σ => ∃ (p : Addr) (n : I32) (fs : List (FieldKey × Value)) (lim : I64),
     args = [.ref p, .int n] ∧ σ.heap p = some (.plain cpCls fs) ∧
     Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) ∧ σ.initOf tpeCls = .done)
  ccrlN ccrlE

/-! ## `getMinSerializedSize(byte)` (executed inline by `checkReadBytesAvailable(TList)`) -/

/-- `getMinSerializedSize(type)`: 8 for DOUBLE (4), 1 for the other type codes it lists; none (a
`TTransportException`) for 5, 7, 9, 16 (UUID) and the rest. -/
def minSize : Nat → Option Nat
  | 0 => some 1 | 1 => some 1 | 2 => some 1 | 3 => some 1 | 4 => some 8 | 6 => some 1
  | 8 => some 1 | 10 => some 1 | 11 => some 1 | 12 => some 1 | 13 => some 1 | 14 => some 1
  | 15 => some 1 | _ => none

theorem instanceFields_tte {P : Program} (hns : NoShadow P)
    (h1 : P.findClass "org.apache.thrift.transport.TTransportException" = some tteC)
    (h2 : P.findClass "org.apache.thrift.TException" = some teC) :
    P.instanceFields "org.apache.thrift.transport.TTransportException" =
      [(("org.apache.thrift.transport.TTransportException", "type_"), .prim .int),
       (("java.lang.Throwable", "detailMessage"), .cls "java.lang.String"),
       (("java.lang.Throwable", "cause"), .cls "java.lang.Throwable")] := by
  have h3 : P.findClass "java.lang.Exception" = none := findClass_of_noShadow hns (by decide)
  have h4 : P.findClass "java.lang.Throwable" = none := findClass_of_noShadow hns (by decide)
  have h5 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  have p3 : preludeFind "java.lang.Exception" = some { name := "java.lang.Exception", isInterface := false, isAbstract := false, super := some "java.lang.Throwable", interfaces := [], fields := [] } := rfl
  have p4 : preludeFind "java.lang.Throwable" = some { name := "java.lang.Throwable", isInterface := false, isAbstract := false, super := some "java.lang.Object", interfaces := ["java.io.Serializable"], fields := [{ name := "detailMessage", ty := (.cls "java.lang.String") }, { name := "cause", ty := (.cls "java.lang.Throwable") }] } := rfl
  have p5 : preludeFind "java.lang.Object" = some { name := "java.lang.Object", isInterface := false, isAbstract := false, super := none, interfaces := [], fields := [] } := rfl
  rw [show P.instanceFields "org.apache.thrift.transport.TTransportException" =
      P.instanceFieldsN (4091 + 1 + 1 + 1 + 1 + 1) "org.apache.thrift.transport.TTransportException" from rfl,
    ifN_step (lookup_prog h1) rfl, ifN_step (lookup_prog h2) rfl, ifN_step (lookup_lib h3 p3) rfl,
    ifN_step (lookup_lib h4 p4) rfl, ifN_last (lookup_lib h5 p5) rfl]
  rfl

/-! ## The message of a `TProtocolException`: `new StringBuilder()` -/

theorem instanceFields_sb {P : Program} (hns : NoShadow P) :
    P.instanceFields "java.lang.StringBuilder" = [] := by
  have h1 : P.findClass "java.lang.StringBuilder" = none := findClass_of_noShadow hns (by decide)
  have h2 : P.findClass "java.lang.AbstractStringBuilder" = none := findClass_of_noShadow hns (by decide)
  have h3 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  rw [show P.instanceFields "java.lang.StringBuilder" =
      P.instanceFieldsN (4093 + 1 + 1 + 1) "java.lang.StringBuilder" from rfl,
    ifN_step (lookup_lib h1 rfl) rfl, ifN_step (lookup_lib h2 rfl) rfl, ifN_last (lookup_lib h3 rfl) rfl]
  rfl

theorem ctorCall_sb {P : Program} (a : Addr) (σ : State) :
    Native.ctorCall P ⟨"java.lang.StringBuilder", .void, "<init>", []⟩ a
        (.plain "java.lang.StringBuilder" []) [] σ =
      some (Native.okVoid (σ.setObj a (.builder "java.lang.StringBuilder" []))) := rfl

/-! ## The closers of `checkContainerReadLength` and `getMinSerializedSize` -/

theorem toInt_toLong (n : I32) : (JInt.toLong n).toInt = n.toInt := by
  unfold JInt.toLong
  exact BitVec.toInt_signExtend_of_le (by decide)

theorem toNat_eq_of_toInt {w : I32} (h0 : 0 ≤ w.toInt) : w.toNat = w.toInt.toNat := by
  have e := BitVec.toInt_eq_toNat_cond w
  have hl := w.isLt
  split at e <;> omega

theorem inLimit_toLong (n : I32) : InLimit (JInt.toLong n) n := Or.inr (Int.le_of_eq (toInt_toLong n).symm)

theorem inLimit_m1 (n : I32) : InLimit 18446744073709551615#64 n := Or.inl (by decide)

theorem inLimit_lt {lim : I64} {n : I32} (h : n.toInt < lim.toInt) : InLimit lim n :=
  Or.inr (Int.le_of_lt h)

theorem eq_of_le_not_lt {lim : I64} {n : I32} (hle : n.toInt ≤ lim.toInt) (hge : ¬ n.toInt < lim.toInt) :
    JInt.toLong n = lim := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_toLong]
  omega

theorem notIn_1 {lim : I64} {n : I32} (hm : lim.toInt < -1) (hge : ¬ n.toInt < lim.toInt)
    (hne : ¬ JInt.toLong n = lim) : ¬ InLimit lim n := by
  rintro (h | h)
  · subst h
    exact absurd hm (by decide)
  · exact hne (eq_of_le_not_lt h hge)

theorem notIn_2 {lim : I64} {n : I32} (hm : ¬ lim = 18446744073709551615#64)
    (hge : ¬ n.toInt < lim.toInt) (hne : ¬ JInt.toLong n = lim) : ¬ InLimit lim n := by
  rintro (h | h)
  · exact hm (h.trans (by decide))
  · exact hne (eq_of_le_not_lt h hge)

theorem ccrl_ok {σ0 : State} {p : Addr} {n : I32} {fs : List (FieldKey × Value)} {lim : I64}
    (hp : σ0.heap p = some (.plain cpCls fs))
    (hl : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (h0 : 0 ≤ n.toInt) (hin : InLimit lim n) : ccrlN [.ref p, .int n] σ0 none σ0 := by
  unfold ccrlN
  intro p' n' he
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨rfl, rfl, fun fs' lim' hp' hl' => ?_⟩
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  rw [hl] at hl'
  simp only [Option.some.injEq, Value.long.injEq] at hl'
  subst hl'
  exact ⟨h0, hin⟩

theorem ccrl_exc {σ0 σ : State} {p : Addr} {n : I32} {fs F : List (FieldKey × Value)} {lim : I64}
    (hp : σ0.heap p = some (.plain cpCls fs))
    (hl : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hc : n.toInt < 0 ∨ ¬ InLimit lim n) (hlt : σ0.next < σ.next) :
    ccrlE [.ref p, .int n] σ0 σ0.next (σ.setObj σ0.next (.plain tpeCls F)) := by
  unfold ccrlE
  intro p' n' he
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨⟨F, setObj_heap_self hlt⟩, fun fs' lim' hp' hl' => ?_⟩
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  rw [hl] at hl'
  simp only [Option.some.injEq, Value.long.injEq] at hl'
  subst hl'
  exact hc

/-- The exception object is the first of the objects the throw path allocates (`omega` does not
read `Addr` facts). -/
theorem lt_add4 (a : Addr) : a < a + 1 + 1 + 1 + 1 :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_add_right _ 3)

theorem lt_add2 (a : Addr) : a < a + 1 + 1 := Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_add_right _ 1)

theorem minSize_lt : ∀ n m, minSize n = some m → n < 16 := by
  intro n m h
  unfold minSize at h
  split at h <;> first | (cases h; decide) | cases h

theorem minSize_none_k {w : I32} {k : Nat} (hk : w.toInt.toNat = k) (hk0 : 0 < k)
    (hm : minSize k = none) : minSize w.toNat = none := by
  rw [toNat_eq_of_toInt (by omega), hk]
  exact hm

theorem minSize_none_neg {w : I32} (hn : ¬ 0 ≤ w.toInt) : minSize w.toNat = none := by
  have e := BitVec.toInt_eq_toNat_cond w
  cases h : minSize w.toNat with
  | none => rfl
  | some m =>
    have := minSize_lt _ _ h
    split at e <;> omega

theorem minSize_none_big {w : I32} (hb : 16 ≤ w.toInt.toNat) : minSize w.toNat = none := by
  have e := BitVec.toInt_eq_toNat_cond w
  cases h : minSize w.toNat with
  | none => rfl
  | some m =>
    have := minSize_lt _ _ h
    split at e <;> omega

/-! ## `checkReadBytesAvailable(TList)` (declared in `TProtocol`) -/

abbrev crbaRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TProtocol».«checkReadBytesAvailable(org.apache.thrift.protocol.TList)».ref

/-- The call `this.checkReadBytesAvailable(list)` in `readListBegin()` (a `TCompactProtocol`
signature; the method is inherited from `TProtocol`). -/
def crbaSig : MethodSig :=
  ⟨cpCls, .void, "checkReadBytesAvailable", [.cls "org.apache.thrift.protocol.TList"]⟩

/-- `checkReadBytesAvailable(list)` returns, changing nothing, when `getMinSerializedSize` lists the
element type (the transport's `checkReadBytesAvailable` changes nothing). -/
def crbaN (args : List Value) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∀ (p l : Addr), args = [.ref p, .ref l] → r = none ∧ σ' = σ ∧
    ∀ (lfs : List (FieldKey × Value)) (b : I32), σ.heap l = some (.plain tlCls lfs) →
      Fields.get lfs (tlCls, "elemType") = some (.int b) → (minSize b.toNat).isSome

/-- Otherwise `getMinSerializedSize` throws a `TTransportException`. -/
def crbaE (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p l : Addr), args = [.ref p, .ref l] → (∃ fs, σ'.heap e = some (.plain ttExcCls fs)) ∧
    ∀ (lfs : List (FieldKey × Value)) (b : I32), σ.heap l = some (.plain tlCls lfs) →
      Fields.get lfs (tlCls, "elemType") = some (.int b) → minSize b.toNat = none

attribute [irreducible] crbaN crbaE

def crbaSpec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p l t tmp : Addr) (lfs : List (FieldKey × Value)) (b s : I32),
     args = [.ref p, .ref l] ∧ CPAtH P R σ p t tmp ∧ σ.heap l = some (.plain tlCls lfs) ∧
     Fields.get lfs (tlCls, "elemType") = some (.int b) ∧ Fields.get lfs (tlCls, "size") = some (.int s) ∧
     σ.initOf ttExcCls = .done)
  crbaN crbaE

def crbaSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p l t tmp : Addr) (lfs : List (FieldKey × Value)) (b s : I32),
     args = [.ref p, .ref l] ∧ CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧ ClassOK P σ t ∧
     σ.heap l = some (.plain tlCls lfs) ∧
     Fields.get lfs (tlCls, "elemType") = some (.int b) ∧ Fields.get lfs (tlCls, "size") = some (.int s) ∧
     σ.initOf ttExcCls = .done)
  crbaN crbaE

theorem crba_ok {σ : State} {p l : Addr} {lfs : List (FieldKey × Value)} {b : I32} {k m : Nat}
    (hl : σ.heap l = some (.plain tlCls lfs)) (he : Fields.get lfs (tlCls, "elemType") = some (.int b))
    (hk : b.toInt.toNat = k) (h0 : 0 ≤ b.toInt) (hm : minSize k = some m) :
    crbaN [.ref p, .ref l] σ none σ := by
  unfold crbaN
  intro p' l' h
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨rfl, rfl, fun lfs' b' hl' he' => ?_⟩
  rw [hl] at hl'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hl'
  subst hl'
  rw [he] at he'
  simp only [Option.some.injEq, Value.int.injEq] at he'
  subst he'
  rw [toNat_eq_of_toInt h0, hk, hm]
  rfl

theorem crba_exc {σ0 σ : State} {p l : Addr} {lfs F : List (FieldKey × Value)} {b : I32}
    (hl : σ0.heap l = some (.plain tlCls lfs)) (he : Fields.get lfs (tlCls, "elemType") = some (.int b))
    (hn : minSize b.toNat = none) (hlt : σ0.next < σ.next) :
    crbaE [.ref p, .ref l] σ0 σ0.next (σ.setObj σ0.next (.plain ttExcCls F)) := by
  unfold crbaE
  intro p' l' h
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨⟨F, setObj_heap_self hlt⟩, fun lfs' b' hl' he' => ?_⟩
  rw [hl] at hl'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hl'
  subst hl'
  rw [he] at he'
  simp only [Option.some.injEq, Value.int.injEq] at he'
  subst he'
  exact hn

/-! ## `readListBegin()` -/

abbrev rlbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readListBegin()».ref

theorem instanceFields_tl {P : Program} (hns : NoShadow P)
    (h1 : P.findClass "org.apache.thrift.protocol.TList" = some tlC) :
    P.instanceFields "org.apache.thrift.protocol.TList" =
      [(("org.apache.thrift.protocol.TList", "elemType"), .prim .byte),
       (("org.apache.thrift.protocol.TList", "size"), .prim .int)] := by
  have h5 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  have p5 : preludeFind "java.lang.Object" = some { name := "java.lang.Object", isInterface := false, isAbstract := false, super := none, interfaces := [], fields := [] } := rfl
  rw [show P.instanceFields "org.apache.thrift.protocol.TList" =
      P.instanceFieldsN (4094 + 1 + 1) "org.apache.thrift.protocol.TList" from rfl,
    ifN_step (lookup_prog h1) rfl, ifN_last (lookup_lib h5 p5) rfl]
  rfl

/-- The new `TList` object (before its constructor). -/
def tlNew : Obj := .plain "org.apache.thrift.protocol.TList"
  [(("org.apache.thrift.protocol.TList", "elemType"), .int 0#32),
   (("org.apache.thrift.protocol.TList", "size"), .int 0#32)]

/-- The size a list header gives: the size nibble, or (nibble 15) the varint after the byte, as
Java's `int`; and the bytes left. `none`: the varint is overlong or truncated. -/
def listSizeJ (u : UInt8) (rest : Bytes) : Option (I32 × Bytes) :=
  if u.toNat / 16 = 15 then (Spec.readVarint 5 rest).map fun q => (BitVec.ofNat 32 q.1, q.2)
  else some (BitVec.ofNat 32 (u.toNat / 16), rest)

/-- The first byte has a known type nibble (`getTType` throws for 14 and 15, with a message built
by string concatenation). -/
def NibbleOKL (src : Bytes) : Prop :=
  ∀ u rest, src = u :: rest → (Spec.ttypeOfCompact (u.toNat % 16)).isSome

/-- The protocol object's `containerLengthLimit_`. -/
def LimitAt (σ : State) (p : Addr) (lim : I64) : Prop :=
  ∃ fs, σ.heap p = some (.plain cpCls fs) ∧
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim)

/-- What `readListBegin()` returns: a new `TList` with the TType of the type nibble and the size
(and the frame facts a caller needs). -/
def rlbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ u rest size rest' tt k l lfs, R.src σ t = u :: rest ∧ listSizeJ u rest = some (size, rest') ∧
      0 ≤ size.toInt ∧ InLimit lim size ∧ Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
      minSize tt = some k ∧ R.src σ' t = rest' ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧
      r = some (.ref l) ∧ σ'.heap l = some (.plain tlCls lfs) ∧
      Fields.get lfs (tlCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get lfs (tlCls, "size") = some (.int size) ∧ σ.next ≤ l ∧ l ≠ t ∧ l ≠ tmp ∧ l ≠ p ∧
      ¬ R.owns σ' t l ∧ PFrame R σ σ' t tmp ∧ OwnsMono R σ σ' t

/-- When `readListBegin()` throws: no byte; a long-form size that is not a varint of at most 5
bytes; a negative size or one above the limit; a type code `getMinSerializedSize` does not list. -/
def rlbE (_P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    (R.src σ t = [] ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)) ∨
    (∃ u rest, R.src σ t = u :: rest ∧ listSizeJ u rest = none ∧
      ((Spec.VarintOverlong 5 rest ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
       (Spec.VarintTruncated 5 rest ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)))) ∨
    (∃ u rest size rest', R.src σ t = u :: rest ∧ listSizeJ u rest = some (size, rest') ∧
      (size.toInt < 0 ∨ ¬ InLimit lim size) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
    (∃ u rest size rest' tt, R.src σ t = u :: rest ∧ listSizeJ u rest = some (size, rest') ∧
      0 ≤ size.toInt ∧ InLimit lim size ∧ Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
      minSize tt = none ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] rlbN rlbE

def rlbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧
     σ.initOf ttExcCls = .done ∧ NibbleOKL (R.src σ t))
  (rlbN P R) (rlbE P R)

/-- The cut points (locals `list` 0, `size_and_type` 1, `size` 2, `this` 3): statement 2, after
`readByte()`: the byte read; statement 7 (`label1`, the call `checkContainerReadLength(size)`): the
size and the bytes left. -/
def rlbInv (P : Program) (R : TRep) : Invariants :=
  [(2, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ u : UInt8, R.src σ0 t = u :: R.src σ t ∧ (Spec.ttypeOfCompact (u.toNat % 16)).isSome ∧
      fr.get 3 = some (.ref p) ∧ fr.get 1 = some (jbyte u) ∧
      σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t),
   (7, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ (u : UInt8) (rest : Bytes) (size : I32), R.src σ0 t = u :: rest ∧
      listSizeJ u rest = some (size, R.src σ t) ∧ (Spec.ttypeOfCompact (u.toNat % 16)).isSome ∧
      fr.get 3 = some (.ref p) ∧ fr.get 1 = some (jbyte u) ∧ fr.get 2 = some (.int size) ∧
      σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t)]

/-- The contracts `readListBegin()` uses: `readByte`, `getTType`, `checkContainerReadLength`,
`checkReadBytesAvailable(TList)`, and `Γ2` (`readVarint32`). -/
def Γ6 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rbSig then some (rbSpecA P R)
  else if sig = gttSig then some gttSpec
  else if sig = ccrlSig then some ccrlSpec
  else if sig = crbaSig then some (crbaSpec P R)
  else Γ2 P R sig

end EquivLean.Demo.Thrift.Java
