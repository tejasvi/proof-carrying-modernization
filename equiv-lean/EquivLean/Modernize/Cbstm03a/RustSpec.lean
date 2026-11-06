import EquivLean.Modernize.Cbstm03a.RustStatement
import EquivLean.Modernize.Cbstm03a.Model

/-!
# CBSTM03A → Rust: the equation of `run`

`RunSpec`: for inputs in the statement's domain, `cbstm03a.run` returns (never panics) an
`Output` holding the outputs of `Model.run` (`Model.lean`):
- `displays`: the displayed lines (Latin-1 bytes = CP037 code points, after dropping the 11 walk
  lines on the COBOL side);
- `stmt_file_writes`: the 80-character `STMT-FILE` lines;
- `html_file_writes`: the 100-character `HTML-FILE` lines;
- `abended`: whether the run abended (`CUSTFILE` or `ACCTFILE` key not found).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbstm03a.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbstm03a.TrnxRecord) (s2 : Slice cbstm03a.CardXrefRecord)
    (s3 : Slice cbstm03a.CustomerRecord) (s4 : Slice cbstm03a.AccountRecord)
    (vals1 vals2 vals3 vals4 : List (List FVal)),
    s1.val.map TrnxRecord.vals = vals1 → s2.val.map CardXrefRecord.vals = vals2 →
    s3.val.map CustomerRecord.vals = vals3 → s4.val.map AccountRecord.vals = vals4 →
    (∀ v ∈ vals1, TrnxRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, CustomerRecord.Valid v) → (∀ v ∈ vals4, AccountRecord.Valid v) →
    EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
    let o := EquivLean.Modernize.Cbstm03a.Model.run vals1 vals2 vals3 vals4
    ∃ out, cbstm03a.run s1 s2 s3 s4 = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.stmt_file_writes.val.map (fun l => l.val.map (·.val)) = o.stmtWrites ∧
      out.html_file_writes.val.map (fun l => l.val.map (·.val)) = o.htmlWrites ∧
      out.abended = o.abended

end EquivLean.Modernize.Cbstm03a.Rust
