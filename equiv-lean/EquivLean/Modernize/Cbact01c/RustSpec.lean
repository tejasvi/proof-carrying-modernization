import EquivLean.Modernize.Cbact01c.RustStatement
import EquivLean.Modernize.Cbact01c.Model

/-!
# CBACT01C → Rust: the equation of `run`

`RunSpec`: for account records with valid field values, `cbact01c.run` returns (never panics)
an `Output` holding the outputs of `Model.run`:
- the displayed lines (Latin-1 = the code points);
- the records written to OUT-FILE and to ARRY-FILE (their field values; an ARRY-FILE record's
  in storage order, the `OCCURS` elements expanded);
- the records written to VBRC-FILE (Latin-1 = the code points of the record's bytes, as a
  DISPLAY line; the length of the `Vec` is the record's length);
- `abended` = false.

The field values of the structs are the generated ones (`RustStatement.lean`).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact01c.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbact01c.AccountRecord) (vals1 : List (List FVal)),
    s1.val.map AccountRecord.vals = vals1 →
    (∀ v ∈ vals1, AccountRecord.Valid v) →
    vals1.length < 2 ^ 28 →
    let o := Model.run vals1
    ∃ out, cbact01c.run s1 = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.out_file_writes.val.map OutAcctRec.vals = o.outWrites ∧
      out.arry_file_writes.val.map ArrArrayRec.vals = o.arryWrites ∧
      out.vbrc_file_writes.val.map (fun l => l.val.map (·.val)) = o.vbrcWrites ∧
      out.abended = false

end EquivLean.Modernize.Cbact01c.Rust
