import EquivLean.Modernize.Cbact04c.Every.RustSpec
import EquivLean.Modernize.Cbact04c.Every.RustRun5
import EquivLean.Modernize.Cbact04c.Every.RustProof

/-!
# CBACT04C → Rust on every input: `run_spec : RunSpec`

`RustRun5.run_specE` proves the equation without any domain, for the record schemas of the
restricted statement (`Cbact04c/RustStatement.lean`); the schemas of `Every/RustStatement.lean` are
the same definitions (generated from the same IR), so `RunSpec` follows.
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact04c.Every.Rust

/-- **The equation of `run` on every input.** -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk h1 h2 h3 h4 hq hclk hclen hv1 hv2 hv3
    hv4 hvq _hdom hlen
  exact EquivLean.Modernize.Cbact04c.Rust.run_specE s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1
    clk h1 h2 h3 h4 hq hclk hclen hv1 hv2 hv3 hv4 hvq hlen

/-- **CBACT04C → Rust, every input** (no lookup assumed to succeed: the abends and the `DEFAULT`
disclosure group retry included): the generated statement (`Every/RustStatement.lean`). -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbact04c.Every.Rust

#print axioms EquivLean.Modernize.Cbact04c.Every.Rust.rust
