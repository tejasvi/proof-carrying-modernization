import EquivLean.Modernize.Cbtrn02c.RustStatement

/-!
# CBTRN02C → Rust: the equation of `run`

`RunSpec`: for valid field values of the four input files (DALYTRAN, XREF, ACCOUNT, TCATBAL, in
SELECT order) in the domain `Domain` (distinct transaction ids, fewer than 10^9 of them), a clock
reading and fewer than 2^28 records, `cbtrn02c.run` returns (never panics) an `Output` holding the
outputs of `Model.run`:
* the displayed lines (Latin-1 = the code points);
* the records written to TRANSACT, DALYREJS and TCATBAL and rewritten in ACCOUNT and TCATBAL (their
  field values);
* RETURN-CODE; `abended` = false.

The record schemas and the structs' field values are the generated statement's (`cobol_schema`,
`rust_record_vals` in `RustStatement.lean`).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbtrn02c.DalytranRecord) (s2 : Slice cbtrn02c.CardXrefRecord)
    (s3 : Slice cbtrn02c.AccountRecord) (s4 : Slice cbtrn02c.TranCatBalRecord)
    (rclk : Std.Array Std.U8 21#usize)
    (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8),
    s1.val.map DalytranRecord.vals = vals1 → s2.val.map CardXrefRecord.vals = vals2 →
    s3.val.map AccountRecord.vals = vals3 → s4.val.map TranCatBalRecord.vals = vals4 →
    rclk.val.map (·.val) = rustLine clk → CurrentDate clk →
    (∀ v ∈ vals1, DalytranRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, AccountRecord.Valid v) → (∀ v ∈ vals4, TranCatBalRecord.Valid v) →
    Domain vals1 vals2 vals3 vals4 →
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
    let o := Model.run vals1 vals2 vals3 vals4 clk
    ∃ out, cbtrn02c.run s1 s2 s3 s4 rclk = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.transact_file_writes.val.map TranRecord.vals = o.tranW ∧
      out.dalyrejs_file_writes.val.map RejectRecord.vals = o.rejW ∧
      out.account_file_rewrites.val.map AccountRecord.vals = o.acctRW ∧
      out.tcatbal_file_writes.val.map TranCatBalRecord.vals = o.catW ∧
      out.tcatbal_file_rewrites.val.map TranCatBalRecord.vals = o.catRW ∧
      out.return_code.val = o.rc ∧
      out.abended = false

end EquivLean.Modernize.Cbtrn02c.Rust
