import EquivLean.Demo.Thrift.Java.Gtt
import EquivLean.Demo.Thrift.Java.FhD

/-!
# Thrift → Java (T4): `readFieldId(byte type)`, the id part of the compact field header reader

`modifier = (type & 0xF0) >> 4`; modifier 0: `readI16()` (the zigzag varint32, cut to a `short`);
else `(short) (lastFieldId_ + modifier)`. A bool type nibble sets `boolValue_`; then
`lastFieldId_ = fieldId`. `readVarint32()` is called through its contract (`Γ2`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rfiRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readFieldId(byte)».ref

/-- Java's unzigzag of an `int` (`zigzagToInt`). -/
def uzzJ (x : I32) : I32 := JInt.ushr x 1#32 ^^^ -(x &&& 1#32)

/-- The delta nibble as Java computes it: `(short) (((short) b & 0xF0) >> 4)`. -/
def modJ (b : I32) : I32 := JInt.toShort (JInt.shr (JInt.toShort b &&& 240#32) 4#32)

/-- The field id `readFieldId(b)` computes after `last`, and the bytes it leaves; `none`: the
long-form varint is overlong or truncated. -/
def fieldIdJ (last b : I32) (src : Bytes) : Option (I32 × Bytes) :=
  if modJ b ≠ 0#32 then some (JInt.toShort (last + modJ b), src)
  else (Spec.readVarint 5 src).map fun q => (JInt.toShort (uzzJ (BitVec.ofNat 32 q.1)), q.2)

/-- The protocol object `p` has a `boolValue_` field. -/
def BoolAt (σ : State) (p : Addr) : Prop :=
  ∃ fs v, σ.heap p = some (.plain cpCls fs) ∧ Fields.get fs (cpCls, "boolValue_") = some v

/-- A `readFieldId` call changed `t`, its objects, `temp`, the fields of `p`, and allocated; `t`
took over no other object. -/
def RFrame (R : TRep) (σ σ' : State) (p t tmp : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
  (∀ a, a < σ.next → a ≠ t → a ≠ tmp → a ≠ p → ¬ R.owns σ t a → σ'.heap a = σ.heap a) ∧
  OwnsMono R σ σ' t

def rfiN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (b last : I32), args = [.ref p, .int b] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    ∃ id rest, fieldIdJ last b (R.src σ t) = some (id, rest) ∧ r = some (.int id) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAt P R σ' p t tmp ∧
      RFrame R σ σ' p t tmp

def rfiE (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (b last : I32), args = [.ref p, .int b] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "lastFieldId_") = some (.int last) →
    fieldIdJ last b (R.src σ t) = none ∧
    ((Spec.VarintOverlong 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
     (Spec.VarintTruncated 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)))

attribute [irreducible] rfiN rfiE

def rfiSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (b last : I32), args = [.ref p, .int b] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ ClassOK P σ t ∧ LastAt σ p last ∧ BoolAt σ p ∧ σ.initOf tpeCls = .done)
  (rfiN P R) (rfiE P R)

end EquivLean.Demo.Thrift.Java
