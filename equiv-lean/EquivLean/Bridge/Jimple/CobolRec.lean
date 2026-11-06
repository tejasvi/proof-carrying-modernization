import EquivLean.Bridge.Cobol.Records
import Jimple
import Cobol.Target.Codepage

/-!
# COBOL records as Java objects (JimpleLean)

The Java translations hold a record of schema `s` (`EquivLean.Cobol.Rec.Schema`) in an object of the
nested class `<Program>$<s.tname>` (e.g. `Cbact02c$CardRecord`) with one field per elementary
item, named `f.jname`: a `long` holding the scaled value of a numeric field, a `String` holding the
CP037-decoded text of an alphanumeric field.  `JRecAt s cls σ v vals`: the value `v` is such an
object in the heap of `σ`, holding the field values `vals`.  A DISPLAY line (bytes in EBCDIC) is a
Java `String` holding its CP037 decoding (`JLineAt`).
-/

open Jimple

namespace EquivLean.Cobol.Rec

/-- The UTF-16 unit of an EBCDIC (CP037) byte. -/
def cp037Unit (b : UInt8) : JChar := BitVec.ofNat 16 (_root_.Cobol.Codepage.cp037Char b).toNat

/-- The Java string of EBCDIC bytes (CP037). -/
def cp037Str (bs : List UInt8) : JStr := bs.map cp037Unit

/-- `v` is a reference to the string `s`. -/
def JStrAt (σ : State) (v : Value) (s : JStr) : Prop :=
  ∃ x, v = .ref x ∧ σ.heap x = some (.str s)

/-- Field `f` of the object with fields `fs` (class `cls`) holds the value `val`. -/
def jFieldAt (σ : State) (cls : ClassName) (fs : List (FieldKey × Value)) (f : Field) :
    FVal → Prop
  | .num v => Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 v))
  | .str bs => ∃ s, Fields.get fs (cls, f.jname) = some s ∧ JStrAt σ s (cp037Str bs)

/-- `v` is an object of class `cls` holding the record with field values `vals`. -/
def JRecAt (s : Schema) (cls : ClassName) (σ : State) (v : Value) (vals : List FVal) : Prop :=
  ∃ x fs, v = .ref x ∧ σ.heap x = some (.plain cls fs) ∧
    Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals

/-- `v` is a Java string holding the CP037 decoding of the line `bs`. -/
def JLineAt (σ : State) (v : Value) (bs : List UInt8) : Prop := JStrAt σ v (cp037Str bs)

end EquivLean.Cobol.Rec
