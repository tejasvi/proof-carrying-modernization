import EquivLean.Bridge.Jimple.CobolRec

/-!
# COBOL records with `OCCURS` items as Java objects

The Java translations hold an elementary item under a one-level `OCCURS` in an array, one per item
of the group (`long[]` for a numeric item, `String[]` for an alphanumeric one), in the field named
`f.jname`; the occurrence `f.idx = [k]` of the item is element `k` (`EquivLean.Cobol.Rec.schemaOf`
expands the occurrences in storage order).  `JRecOccAt` is `JRecAt` with such fields read from the
arrays.  Kept apart from `CobolRec`, so that the statements of records without `OCCURS` do not
depend on it.
-/

open Jimple

namespace EquivLean.Cobol.Rec

/-- The Java value `e` holds the field value `val`: a `long` holding the scaled value of a numeric
item, a string holding the CP037 decoding of an alphanumeric one. -/
def jValAt (σ : State) (e : Value) : FVal → Prop
  | .num v => e = .long (BitVec.ofInt 64 v)
  | .str bs => JStrAt σ e (cp037Str bs)

/-- Field `f` of the object with fields `fs` (class `cls`) holds the value `val`: as in `jFieldAt`
for an item not under `OCCURS`; element `k` of the array in the field for the occurrence
`f.idx = [k]` (no nested `OCCURS`). -/
def jFieldOccAt (σ : State) (cls : ClassName) (fs : List (FieldKey × Value)) (f : Field)
    (val : FVal) : Prop :=
  match f.idx with
  | [] => jFieldAt σ cls fs f val
  | [k] => ∃ a et xs, Fields.get fs (cls, f.jname) = some (.ref a) ∧
      σ.heap a = some (.array et xs) ∧ jValAt σ (xs.getD k .null) val
  | _ :: _ :: _ => False

/-- `v` is an object of class `cls` holding the record with field values `vals`, the items under
`OCCURS` in arrays. -/
def JRecOccAt (s : Schema) (cls : ClassName) (σ : State) (v : Value) (vals : List FVal) : Prop :=
  ∃ x fs, v = .ref x ∧ σ.heap x = some (.plain cls fs) ∧
    Forall2 (fun f val => jFieldOccAt σ cls fs f val) s.fields vals

end EquivLean.Cobol.Rec
