import EquivLean.Demo.Thrift.Java.Gam2

/-!
# Thrift → Java (T4): field header facts shared by the writer and the reader
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev tfC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TField»

def tfCls : ClassName := "org.apache.thrift.protocol.TField"

/-- `f` is a `TField` with id `id` (a `short`). -/
def FieldIdAt (σ : State) (f : Addr) (id : I32) : Prop :=
  ∃ ffs, σ.heap f = some (.plain tfCls ffs) ∧ Fields.get ffs (tfCls, "id") = some (.int id)

/-- The protocol object `p` has `lastFieldId_ = last`. -/
def LastAt (σ : State) (p : Addr) (last : I32) : Prop :=
  ∃ fs, σ.heap p = some (.plain cpCls fs) ∧ Fields.get fs (cpCls, "lastFieldId_") = some (.int last)

/-- A field-header write changed only `t`, its objects, `temp` and `p` (`lastFieldId_`). -/
def WFrame (R : TRep) (σ σ' : State) (p t tmp : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
  (∀ a, a < σ.next → a ≠ t → a ≠ tmp → a ≠ p → ¬ R.owns σ t a → σ'.heap a = σ.heap a)

end EquivLean.Demo.Thrift.Java
