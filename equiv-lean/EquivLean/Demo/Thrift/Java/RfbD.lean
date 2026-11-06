import EquivLean.Demo.Thrift.Java.Rfi
import EquivLean.Demo.Thrift.Java.Rb

/-!
# Thrift → Java (T4): `readFieldBegin()`, definitions

`type = readByte()`; the byte 0: the static `TSTOP`; else `new TField("", getTType(type & 0x0F),
readFieldId(type))`. The callees are used through their proved contracts (`Γ3`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rfbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readFieldBegin()».ref

def rbSig : MethodSig := ⟨cpCls, .prim .byte, "readByte", []⟩
def gttSig : MethodSig := ⟨cpCls, .prim .byte, "getTType", [.prim .byte]⟩
def rfiSig : MethodSig := ⟨cpCls, .prim .short, "readFieldId", [.prim .byte]⟩

theorem instanceFields_tf {P : Program} (hns : NoShadow P)
    (h1 : P.findClass "org.apache.thrift.protocol.TField" = some tfC) :
    P.instanceFields "org.apache.thrift.protocol.TField" =
      [(("org.apache.thrift.protocol.TField", "name"), .cls "java.lang.String"),
       (("org.apache.thrift.protocol.TField", "type"), .prim .byte),
       (("org.apache.thrift.protocol.TField", "id"), .prim .short)] := by
  have h5 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  have p5 : preludeFind "java.lang.Object" = some { name := "java.lang.Object", isInterface := false, isAbstract := false, super := none, interfaces := [], fields := [] } := rfl
  rw [show P.instanceFields "org.apache.thrift.protocol.TField" =
      P.instanceFieldsN (4094 + 1 + 1) "org.apache.thrift.protocol.TField" from rfl,
    ifN_step (lookup_prog h1) rfl, ifN_last (lookup_lib h5 p5) rfl]
  rfl

/-- The new `TField` object (before its constructor). -/
def tfNew : Obj := .plain "org.apache.thrift.protocol.TField"
  [(("org.apache.thrift.protocol.TField", "name"), .null),
   (("org.apache.thrift.protocol.TField", "type"), .int 0#32),
   (("org.apache.thrift.protocol.TField", "id"), .int 0#32)]

/-- `readByte()` for the callers: the protocol object named by its fields, `CPAt` folded after
the call. -/
def rbNA (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∃ u rest, R.src σ t = u :: rest ∧ r = some (jbyte u) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ CPAtH P R σ' p t tmp ∧ PFrame R σ σ' t tmp ∧ OwnsMono R σ σ' t

def rbEA (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    R.src σ t = [] ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs))

def rbSpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp)
  (rbNA P R) (rbEA P R)

/-- `readFieldId(b)` for the callers. -/
def rfiNA (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (b last : I32), args = [.ref p, .int b] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    ∃ id rest, fieldIdJ last b (R.src σ t) = some (id, rest) ∧ r = some (.int id) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAtH P R σ' p t tmp ∧
      RFrame R σ σ' p t tmp

def rfiEA (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (b last : I32), args = [.ref p, .int b] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    fieldIdJ last b (R.src σ t) = none ∧
    ((Spec.VarintOverlong 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
     (Spec.VarintTruncated 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)))

def rfiSpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (b last : I32), args = [.ref p, .int b] ∧ CPAt P R σ p t tmp ∧
     LastAt σ p last ∧ BoolAt σ p ∧ σ.initOf tpeCls = .done)
  (rfiNA P R) (rfiEA P R)

/-- The contracts `readFieldBegin()` uses: `readByte`, `getTType`, `readFieldId`, and `Γ2`. -/
def Γ3 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rbSig then some (rbSpecA P R)
  else if sig = gttSig then some gttSpec
  else if sig = rfiSig then some (rfiSpecA P R)
  else Γ2 P R sig

/-- The first byte, unless 0, has a known compact type nibble (nibbles 14 and 15 make
`getTType` throw, with a message built by string concatenation). -/
def NibbleOK (src : Bytes) : Prop :=
  ∀ u rest, src = u :: rest → u.toNat ≠ 0 → (Spec.ttypeOfCompact (u.toNat % 16)).isSome

/-- What `readFieldBegin()` returns: for the byte 0 the static `TSTOP`; else a new `TField` with
the TType of the type nibble and the id `readFieldId` computes. -/
def rfbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (last : I32), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    ∃ u rest, R.src σ t = u :: rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧
      RFrame R σ σ' p t tmp ∧
      ((u.toNat = 0 ∧ r = some ((σ.static (cpCls, "TSTOP")).getD .null) ∧ R.src σ' t = rest ∧
          LastAt σ' p last) ∨
       (u.toNat ≠ 0 ∧ ∃ tt id rest' r0 ffs, Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
          fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest = some (id, rest') ∧
          R.src σ' t = rest' ∧ r = some (.ref r0) ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
          Fields.get ffs (tfCls, "type") = some (.int (BitVec.ofNat 32 tt)) ∧
          Fields.get ffs (tfCls, "id") = some (.int id) ∧ LastAt σ' p id))

/-- When `readFieldBegin()` throws: no byte, or the long-form id is not a varint of at most 5
bytes. -/
def rfbE (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (last : I32), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    (R.src σ t = [] ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)) ∨
    (∃ u rest, R.src σ t = u :: rest ∧ u.toNat ≠ 0 ∧
      fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest = none ∧
      ((Spec.VarintOverlong 5 rest ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
       (Spec.VarintTruncated 5 rest ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))))

attribute [irreducible] rfbN rfbE

def rfbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (last : I32), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LastAt σ p last ∧ BoolAt σ p ∧ σ.initOf tpeCls = .done ∧
     σ.initOf cpCls = .done ∧ σ.initOf tfCls = .done ∧ NibbleOK (R.src σ t))
  (rfbN P R) (rfbE P R)

/-- At the call `readFieldId(type)` (statement 8; locals `$s3` 0, `type` 1, `$b1` 2, `$r0` 3,
`this` 4): the byte read, its TType, the new `TField`, and the state facts. -/
def rfbInv (P : Program) (R : TRep) : Invariants :=
  [(8, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (last : I32), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    ∃ (u : UInt8) (tt : Nat) (r0 : Addr),
      R.src σ0 t = u :: R.src σ t ∧ u.toNat ≠ 0 ∧ Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
      fr.get 4 = some (.ref p) ∧ fr.get 1 = some (jbyte u) ∧ fr.get 3 = some (.ref r0) ∧
      fr.get 2 = some (.int (BitVec.ofNat 32 tt)) ∧
      σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      σ.heap r0 = some tfNew ∧ r0 ≠ t ∧ r0 ≠ tmp ∧ r0 ≠ p ∧ ¬ R.owns σ t r0 ∧ σ0.next ≤ r0 ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t)]

end EquivLean.Demo.Thrift.Java
