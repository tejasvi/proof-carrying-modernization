import EquivLean.Modernize.Cbtrn03c.RustStatement

/-!
# CBTRN03C → Rust: the equation of `run`

The inputs are the five input files of CBTRN03C in SELECT order (TRANSACT-FILE, XREF-FILE,
TRANTYPE-FILE, TRANCATG-FILE, DATE-PARMS-FILE; REPORT-FILE, the fifth SELECT, is the output), as
Rust slices of the records the program reads INTO (`mapping.json`).  `RunSpec`: for valid field
values in the domain `Domain` (fewer than `2 ^ 28` records in all), `cbtrn03c.run` returns (never
panics) an `Output` with the outputs of `Model.run`:
- the displayed lines (Latin-1 = the code points);
- the report records written (their field values);
- `abended`.

The record schemas and the structs' field values are the generated statement's (`cobol_schema`,
`rust_record_vals` in `RustStatement.lean`).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn03c.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (s5 : Slice cbtrn03c.WsDateparmRecord) (vals1 vals2 vals3 vals4 vals5 : List (List FVal)),
    s1.val.map TranRecord.vals = vals1 → s2.val.map CardXrefRecord.vals = vals2 →
    s3.val.map TranTypeRecord.vals = vals3 → s4.val.map TranCatRecord.vals = vals4 →
    s5.val.map WsDateparmRecord.vals = vals5 →
    (∀ v ∈ vals1, TranRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, TranTypeRecord.Valid v) → (∀ v ∈ vals4, TranCatRecord.Valid v) →
    (∀ v ∈ vals5, WsDateparmRecord.Valid v) →
    Domain vals1 vals2 vals3 vals4 vals5 →
    vals1.length + vals2.length + vals3.length + vals4.length + vals5.length < 2 ^ 28 →
    let o := Model.run vals1 vals2 vals3 vals4 vals5
    ∃ out, cbtrn03c.run s1 s2 s3 s4 s5 = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.report_file_writes.val.map FdReptfileRec.vals = o.writes ∧
      out.abended = o.abended

end EquivLean.Modernize.Cbtrn03c.Rust
