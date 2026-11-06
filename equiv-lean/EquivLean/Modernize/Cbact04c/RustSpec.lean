import EquivLean.Modernize.Cbact04c.RustStatement
import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C → Rust: the equation of `run`

`RunSpec`: for inputs in the statement's domain, `cbact04c_t.run` returns (never panics) an
`Output` holding the outputs of `Model.run`:
- the displayed lines (Latin-1 = the code points);
- the transactions written and the accounts rewritten (their field values);
- `abended` = false.

`RustProof.lean` derives the generated statement from this equation.
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact04c.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbact04c_t.TranCatBalRecord) (s2 : Slice cbact04c_t.CardXrefRecord)
    (s3 : Slice cbact04c_t.AccountRecord) (s4 : Slice cbact04c_t.DisGroupRecord)
    (q1 : cbact04c_t.ExternalParms) (rclk : Std.Array Std.U8 21#usize)
    (vals1 vals2 vals3 vals4 : List (List FVal)) (link1 : List FVal) (clk : List UInt8),
    s1.val.map TranCatBalRecord.vals = vals1 → s2.val.map CardXrefRecord.vals = vals2 →
    s3.val.map AccountRecord.vals = vals3 → s4.val.map DisGroupRecord.vals = vals4 →
    ExternalParms.vals q1 = link1 → rclk.val.map (·.val) = rustLine clk → clk.length = 21 →
    (∀ v ∈ vals1, TranCatBalRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, AccountRecord.Valid v) → (∀ v ∈ vals4, DisGroupRecord.Valid v) →
    ExternalParms.Valid link1 → Domain vals1 vals2 vals3 vals4 link1 →
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
    let o := Model.run vals1 vals2 vals3 vals4 (Model.parmOf link1) clk
    ∃ out, cbact04c_t.run s1 s2 s3 s4 q1 rclk = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.transact_file_writes.val.map TranRecord.vals = o.writes ∧
      out.account_file_rewrites.val.map AccountRecord.vals = o.rewrites ∧
      out.abended = false

end EquivLean.Modernize.Cbact04c.Rust
