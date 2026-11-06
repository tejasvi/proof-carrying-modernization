import Lean

/-!
# The relational specification database

A theorem tagged `@[equiv_spec]` states a simulation between two calls,
`Sim R (f_target args) (f_source args')`, usually proved once for a pair of loops or helper
functions.  `equiv_call` uses it at every pair of matching calls (through `Sim.wp_cut`), so a
caller's proof never re-executes the callees: proofs are modular, and a change to one function
needs only its own relational proof checked again.
-/

register_label_attr equiv_spec
