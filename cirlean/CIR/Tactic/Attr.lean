import Lean

/-! Simp sets used by the verification tactics. -/

/-- Rewrite rules for one step of symbolic execution (see `cir_vcg`). -/
register_simp_attr cir_exec

/-- Rules for simplifying the pure goals left by symbolic execution. -/
register_simp_attr cir_pure

/-- Function specifications (theorems concluding `Returns ctx sym args m post`)
used by `cir_vcg` at call sites instead of inlining the callee. -/
register_label_attr cir_spec

/-- Pointer arithmetic on array / container elements (iterators): added to
the symbolic execution simp set only on goals that mention it. -/
register_simp_attr cir_iter
