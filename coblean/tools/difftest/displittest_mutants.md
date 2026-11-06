# displittest.py: planted errors (mutants of DISPLAY of a numeric literal)

Each mutant is one exact text replacement, made in a separate copy of the tree, never in the work
tree: in `Cobol/Sem/Exec.lean` (`displayBytes` of a numeric literal,
`else .ok (digitChars c (max (if n = 0 then numDigits v.natAbs else n) (max s.toNat 1)) v.natAbs)`)
or in `tools/cobolfe/parser.py` (`st_DISPLAY`'s check for a signed literal,
`if any(o.kind == "num" and str(o.tok.val)[:1] in "+-" for o in ops):`). Then `lake build cobolrun`
in that copy (for the Lean mutant) and `displittest.py --root <copy> --n 60 --seed 1`. The fixed tree
passes 60 of 60 programs at seed 1.

| id | replacement | what it plants | seed 1 |
|---|---|---|---|
| MC1 | `(max (if n = 0 then numDigits v.natAbs else n) (max s.toNat 1))` -> `(max (numDigits v.natAbs) 1)` | the literal's leading zeros dropped (`0.05` as `5`) | mismatch 46, ok-unsup 13, ok 1: caught |
| MC2 | `in "+-"` -> `in "+"` | a literal with `-` not reported by the front end (the model's own fault at run time instead) | lean-signal 6, ok 47, ok-unsup 7: caught |

How they were run (2026-10-28, helper editpoint-fix): `~/coblean_runs/editfix/scripts/run_mutant_ef_v4.sh
REF FILE ID displittest` in `~/coblean_runs/editfix/mut/tree` (REF `Exec.lean.C` or `parser.py.C`).
The unified diffs are `mut/ID.diff`.
