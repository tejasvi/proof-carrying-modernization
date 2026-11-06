import EquivLean.Modernize.Cbtrn02c.Any.RustSpec
import EquivLean.Modernize.Cbtrn02c.Any.RustRun2
import EquivLean.Modernize.Cbtrn02c.Any.RustProof

/-!
# CBTRN02C → Rust on any input: `run_spec : RunSpec`

`Any/RustRun2.run_specX` proves the equation without any domain, for the record schemas of the
restricted statement (`Cbtrn02c/RustStatement.lean`); the schemas of `Any/RustStatement.lean` are
the same definitions (generated from the same IR), so `RunSpec` follows, and with
`Any/RustProof.statement_of_run` the generated statement.
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn02c.Any.Rust

/-- **The equation of `run` on any input.** -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk h1 h2 h3 h4 hclk hcd hv1 hv2 hv3 hv4 _hdom hsz
  exact EquivLean.Modernize.Cbtrn02c.Rust.run_specX s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk
    h1 h2 h3 h4 hclk hcd hv1 hv2 hv3 hv4 hsz

/-- **CBTRN02C → Rust, any input** (repeated transaction ids included: the abend at a written id):
the generated statement (`Any/RustStatement.lean`). -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbtrn02c.Any.Rust

#print axioms EquivLean.Modernize.Cbtrn02c.Any.Rust.rust
