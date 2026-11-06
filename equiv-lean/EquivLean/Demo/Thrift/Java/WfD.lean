import EquivLean.Demo.Thrift.Java.FhR

/-!
# Thrift → Java (T4): the compact field header writer, definitions

`writeFieldBeginInternal(field, typeOverride)` with a type override (a compact type nibble): the
byte `(id - last) << 4 | ty` (`writeByteDirect(int)`) when `id > last` and `id - last ≤ 15`, else
the byte `ty` (`writeByteDirect(byte)`) and `writeI16(id)` (the zigzag varint of `id`); then
`lastFieldId_ = id`. `writeByteDirect(byte)` and `writeI16(short)` are used through their proved
contracts, `writeByteDirect(int)` is executed inline.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev wbdRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeByteDirect(byte)».ref
abbrev wi16Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeI16(short)».ref
abbrev wfbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeFieldBeginInternal(org.apache.thrift.protocol.TField,byte)».ref

def wbdSig : MethodSig := ⟨cpCls, .void, "writeByteDirect", [.prim .byte]⟩
def wi16Sig : MethodSig := ⟨cpCls, .void, "writeI16", [.prim .short]⟩
def gctSig : MethodSig := ⟨cpCls, .prim .byte, "getCompactType", [.prim .byte]⟩

/-- `writeByteDirect(b)`: appends the byte `b`. -/
def wbdN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (b : I32), args = [.ref p, .int b] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    r = none ∧ R.sink σ' t = R.sink σ t ++ [UInt8.ofNat b.toNat] ∧ R.src σ' t = R.src σ t ∧
      CPAtH P R σ' p t tmp ∧ σ'.heap p = some (.plain cpCls fs) ∧ PFrame R σ σ' t tmp ∧
      OwnsMono R σ σ' t

def wbdSpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (b : I32), args = [.ref p, .int b] ∧ CPAt P R σ p t tmp)
  (wbdN P R) (fun _ _ _ _ => False)

def wbdSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (b : I32), args = [.ref p, .int b] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ ClassOK P σ t)
  (wbdN P R) (fun _ _ _ _ => False)

/-- `writeI16(i)`: appends the zigzag varint of `i`. -/
def wi16N (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (i : I32), args = [.ref p, .int i] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    r = none ∧ R.sink σ' t = R.sink σ t ++ Spec.varint (Spec.zigzag i.toInt) ∧
      R.src σ' t = R.src σ t ∧ CPAtH P R σ' p t tmp ∧ σ'.heap p = some (.plain cpCls fs) ∧
      PFrame R σ σ' t tmp

def wi16SpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (i : I32), args = [.ref p, .int i] ∧ CPAt P R σ p t tmp)
  (wi16N P R) (fun _ _ _ _ => False)

def wi16SpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (i : I32), args = [.ref p, .int i] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp)
  (wi16N P R) (fun _ _ _ _ => False)

attribute [irreducible] wbdN wi16N

/-- `getCompactType` is called only for the type override `-1`, which the writer's
precondition excludes: its contract here has the precondition `False`. -/
def gctSpec : Spec := Spec.of (fun _ _ => False) (fun _ _ _ _ => True) (fun _ _ _ _ => True)

/-- The contracts `writeFieldBeginInternal` uses. -/
def Γ4 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = wbdSig then some (wbdSpecA P R)
  else if sig = wi16Sig then some (wi16SpecA P R)
  else if sig = gctSig then some gctSpec
  else Γ2 P R sig

/-- The write facts that the symbolic execution keeps out of sight (simp loops on them):
`id` and `last` are `short`s, `ty` a nibble. -/
def WfbFacts (id last ty : I32) : Prop :=
  JInt.toShort id = id ∧ JInt.toShort last = last ∧ ty.toNat < 16

/-- What `writeFieldBeginInternal(f, ty)` guarantees: it appends `fieldHeader last id ty` and
sets `lastFieldId_ = id`. -/
def wfbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp f : Addr) (fs ffs : List (FieldKey × Value)) (ty id last : I32),
    args = [.ref p, .ref f, .int ty] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    σ.heap f = some (.plain tfCls ffs) → Fields.get ffs (tfCls, "id") = some (.int id) →
    r = none ∧ R.sink σ' t = R.sink σ t ++ Spec.fieldHeader last.toInt id.toInt ty.toNat ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp ∧ LastAt σ' p id ∧ WFrame R σ σ' p t tmp

attribute [irreducible] wfbN

def wfbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp f : Addr) (ty id last : I32), args = [.ref p, .ref f, .int ty] ∧
     CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧ FieldIdAt σ f id ∧ LastAt σ p last ∧
     Hide (WfbFacts id last ty) ∧ f ≠ t ∧ f ≠ tmp ∧ f ≠ p ∧ ¬ R.owns σ t f)
  (wfbN P R) (fun _ _ _ _ => False)

/-- At `label3` (statement 32; locals `$s1` 0, `$s2` 1, `typeOverride` 2, `$i5` 3, `$i16` 4,
`field` 5, `this` 6): the header is written. -/
def wfbInv (P : Program) (R : TRep) : Invariants :=
  [(32, fun args σ0 fr σ =>
    ∀ (p t tmp f : Addr) (fs ffs : List (FieldKey × Value)) (ty id last : I32),
    args = [.ref p, .ref f, .int ty] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    σ0.heap f = some (.plain tfCls ffs) → Fields.get ffs (tfCls, "id") = some (.int id) →
    fr.get 6 = some (.ref p) ∧ fr.get 5 = some (.ref f) ∧
      σ.heap p = some (.plain cpCls fs) ∧ σ.heap f = some (.plain tfCls ffs) ∧
      CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ++ Spec.fieldHeader last.toInt id.toInt ty.toNat ∧
      R.src σ t = R.src σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a))]

end EquivLean.Demo.Thrift.Java
