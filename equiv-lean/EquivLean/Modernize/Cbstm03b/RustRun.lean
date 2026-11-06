import EquivLean.Modernize.Cbstm03b.RustCall
import EquivLean.Modernize.Cbstm03b.RustProof

/-!
# CBSTM03B → Rust: the statement

`call_spec : CallSpec` (`RustCall.lean`): on inputs with `CallHyp`, the translation's `call` returns (no panic)
the model's state and area. `rust : Statement`: with the statement side (`RustProof.statement_of_call`).
-/

namespace EquivLean.Modernize.Cbstm03b.Rust

/-- **CBSTM03B → Rust, one call, every input** (in the statements' domain). -/
theorem rust : Statement := statement_of_call call_spec

end EquivLean.Modernize.Cbstm03b.Rust

#print axioms EquivLean.Modernize.Cbstm03b.Rust.call_spec
#print axioms EquivLean.Modernize.Cbstm03b.Rust.rust
