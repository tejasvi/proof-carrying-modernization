# editpttest.py: planted errors (Lean mutants of the M-editpoint fix)

Each mutant is one exact text replacement in `Cobol/Edit.lean` (the text occurs once), made in a
separate copy of the tree, never in the work tree: the condition for an insertion character in
`editOpt.gen`,

    if j ≤ k0 ∧ (j < i ∨ (j = i ∧ 0 < i ∧ rest.any (fun p => p == .point || p == .implied))) then

Then `lake build cobolrun` in that copy, `editpttest.py --root <copy> --n 60 --seed 1` and the hand
cases `editpt_cases/v_editpt1.cob` (`--run`). The fixed tree passes 60 of 60 programs at seed 1
(ok-g 58, ok 2) and agrees with GnuCOBOL on all 36 hand-case lines. (This table was measured with
the tester as it was before the M-editlead change below, which also changed its generation.)

| id | the condition becomes | what it plants | seed 1 | v_editpt1.cob |
|---|---|---|---|---|
| M1 | `j ≤ k0 ∧ j < i` | the version before the fix (M-editpoint) | mismatch 60: caught | 16 lines differ (E07 E08 E10 E12 E14-E16 E18-E23 E25-E27) |
| M2 | `j ≤ k0 ∧ (j < i ∨ (j = i ∧ 0 < i))` | insertion characters right after the decimal point replaced too | mismatch 30, ok-g 29, ok 1: caught | E31 E32 |
| M3 | `j ≤ k0 ∧ (j < i ∨ (j = i ∧ rest.any …))` | an insertion character before the point replaced when there is no integer digit position (the string is right of the point) | survives (every generated picture has integer digit positions) | E33-E36: caught |
| M4 | `… rest.any (fun p => p == .point)` | the case missed before an implied decimal point `V` | mismatch 41, ok-g 19: caught | E22 |

How they were run (2026-10-28, helper editpoint-fix): `~/coblean_runs/editfix/scripts/run_mutant_ef_v2.sh ID`
(restore `Edit.lean`, apply `mut/ID.old` -> `mut/ID.new` with `mutate_ef_v1.py`, build, run, restore,
sha256 checked) in `~/coblean_runs/editfix/mut/tree`, a copy of the fixed tree. The unified diffs
are `mut/ID.diff`.

## M-editlead (2026-10-28, second change)

The condition became

    if j ≤ k0 ∧ (0 < j ∨ ([some .cs, some .plus, some .minus].contains suppKind ∧
          rest.all (· != .floatHead))) ∧
        (j < i ∨ (j = i ∧ 0 < i ∧ rest.any (fun p => p == .point || p == .implied))) then

(an insertion character with no digit position on its left is part of the string only after the
first symbol of a floating string), and the tester generates an insertion character left of the
string in a fifth of its pictures. The fixed tree passes 60 of 60 programs at seed 1 (ok-g 60) and
agrees with GnuCOBOL on all 48 lines of `v_editpt1.cob` and `v_editlead.cob`; the tree before this
change (the first fix only) fails 45 of the 60. Mutants of the new disjunct, run as above with
`run_mutant_ef_v3.sh Edit.lean.D ID` (hand cases `v_editpt1.cob` and `v_editlead.cob`):

| id | the disjunct becomes | what it plants | seed 1 | hand cases |
|---|---|---|---|---|
| MD1 | `0 < j ∨ [some .cs, some .plus, some .minus].contains suppKind` | a character left of a floating string's first symbol replaced | mismatch 18, ok-g 42: caught | v_editlead L04 L08 L11 L12 |
| MD2 | `0 < j` | a character right after a floating string's first symbol written | mismatch 43, ok-g 17: caught | v_editlead L09 L10 |
| MD4 | `0 < j ∨ rest.all (· != .floatHead)` | a character left of a `Z` or `*` string replaced (as before the change) | mismatch 36, ok-g 24: caught | v_editlead L01-L03 L05-L07 |
