import Lean

/-!
# Simp set of the COBOL bridge

`cobol_aeneas`: Aeneas' checked scalar operations, casts, binds and `wp` evaluation, stated as
rewrite rules for coblean's symbolic executor (`Bridge/Cobol/Tactic.lean`).
-/

register_simp_attr cobol_aeneas
