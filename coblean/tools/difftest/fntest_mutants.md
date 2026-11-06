# Planted faults for the intrinsic-function testers

The README's control for `fntest_num.py`, `fntest_date.py` and `fntest_alnum.py` (the paragraph
"Intrinsic functions are tested by three generators") plants one fault per tester in the Lean model
and counts the programs the tester then fails ("kills"; every kill had status `mismatch`). This
file gives the exact faults, the trees they were applied to, the commands and the counts.

## The faults

Each fault is a one-line unified diff, applied from the tree root with `patch -p1`. All three
change Lean sources, so `cobolrun` must be rebuilt (`LRUN_AS=67108864 scripts/lrun.sh lake build
cobolrun`: 88 jobs in a built copy of live). The faults are independent: `fntest_num.py` generates
`FACTORIAL`, `SUM`, `RANGE` and `LENGTH`, `fntest_date.py` only the four integer-date functions,
and `fntest_alnum.py` `UPPER-CASE`, `LOWER-CASE`, `REVERSE`, `LENGTH` and `WHEN-COMPILED`; the
patched lines are reached only through `RANGE`, the date functions and `UPPER-CASE`
respectively. A tree with all three patches therefore gives each tester the same result as a tree
with its own patch alone. The diffs are also in `~/coblean_runs/ifn/mutants/` (`range_sign.diff`,
`leap_century.diff`, `lower_z.diff`, and `leap_readme_literal.diff` for the variant).

### 1. `RANGE` sign (`fntest_num.py`)

```diff
--- a/Cobol/Frontend/Resolve.lean
+++ b/Cobol/Frontend/Resolve.lean
@@ -169,7 +169,7 @@
     | "MAX", a :: rest => pure (rest.foldl .max a)
     -- IBM: SUM adds the arguments in order to 0; RANGE subtracts MIN from MAX (exact)
     | "SUM", a :: rest => pure (rest.foldl .add a)
-    | "RANGE", a :: rest => pure (.sub (rest.foldl .max a) (rest.foldl .min a))
+    | "RANGE", a :: rest => pure (.sub (rest.foldl .min a) (rest.foldl .max a))
     | "FACTORIAL", [a] => pure (.factorial a)
     | "INTEGER-OF-DATE", [a] => pure (.dateFn .integerOfDate a)
     | "DATE-OF-INTEGER", [a] => pure (.dateFn .dateOfInteger a)
```

`RANGE` becomes `MIN - MAX` instead of `MAX - MIN`: every non-zero result changes sign.

### 2. Century leap years (`fntest_date.py`)

```diff
--- a/Cobol/Sem/Arith.lean
+++ b/Cobol/Sem/Arith.lean
@@ -92,7 +92,7 @@
   else if x % 10 ^ s.toNat = 0 then some (x / 10 ^ s.toNat) else none
 
 /-- Gregorian leap year. -/
-def leapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
+def leapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 1 || y % 400 == 0)
 
 /-- Days of month `m` (1-12) of year `y`. -/
 def monthDays (y m : Nat) : Nat :=
```

`y % 100 != 1` holds for every multiple of 4, so the patched `leapYear y` is `y % 4 == 0`: every
century year is a leap year, not only those divisible by 400. Within the functions' domain that
adds 63 years: 1700, 1800, 1900, 2100, 2200, 2300, 2500, ... 9900. `leapYear` decides the length of
February and the last valid day of a `YYYYDDD` year. The fault is not "1700, 1800 and 1900 only":
that narrower variant (end of this file) kills fewer programs.

### 3. Lowercase `z` (`fntest_alnum.py`)

```diff
--- a/Cobol/Sem/Data.lean
+++ b/Cobol/Sem/Data.lean
@@ -189,7 +189,7 @@
 their EBCDIC positions, whatever the code page); every other character is unchanged. -/
 def upperByte (c : Config) (b : UInt8) : UInt8 :=
   match c.charset with
-  | .ascii => if 0x61 ≤ b && b ≤ 0x7A then b - 0x20 else b
+  | .ascii => if 0x61 ≤ b && b < 0x7A then b - 0x20 else b
   | .ebcdic =>
     if (0x81 ≤ b && b ≤ 0x89) || (0x91 ≤ b && b ≤ 0x99) || (0xA2 ≤ b && b ≤ 0xA9) then b + 0x40
     else b
```

With the ASCII character set, `UPPER-CASE` leaves `z` (0x7A) unchanged. `LOWER-CASE` and the
EBCDIC mapping are unaffected (`fntest_alnum.py` runs the ASCII profile only).

## Runs and kill counts

Programs come from `random.Random(seed)`, 60 per run with 20 statements each (the testers'
defaults), so a run is fixed by the tester's source, the seed and the tree.

| Tester | Fault | seed 1, 2026-10-27 00:42Z | seed 1, 06:17Z | seed 2, 06:17Z |
|---|---|---|---|---|
| `fntest_num.py` | `RANGE` sign | 59 of 60 | 59 | 60 |
| `fntest_date.py` | century leap years | 33 of 60 | 33 | 25 |
| `fntest_alnum.py` | lowercase `z` | 11 of 60 | 11 | 20 |

Unpatched, all three agree with GnuCOBOL on 60 of 60 programs at both seeds (evidence rows
V.fn.*).

**00:42Z (the counts in the README).** Tree `~/coblean_ifn_mut`: a `cp -a` of the ifn scratch
`~/coblean_ifn` (snapshot `coblean-20261026T1055Z` plus the intrinsic-function change) made at
about 00:36Z, with all three faults applied together; the diffs above are `diff -u` of its three
files against the scratch's. Its `tools/cobolfe/parser.py` was the final one, and `cobolrun` was
rebuilt there (88 jobs). The command ran under `~/coblean_runs/g.sh ifn_mut_tests2`, for `t` in
`num date alnum`; the literal line was not saved, and these parameters follow from the guard log,
the output directories and the programs kept:

    python3 -I -B ~/coblean_ifn/tools/difftest/fntest_$t.py --root ~/coblean_ifn_mut \
        --out ~/coblean_runs/ifn/mut2/$t --n 60 --seed 1 --show 1

The testers were the final versions, byte-identical to the ones in this directory: the kept
`fntest_alnum.py` programs contain `FUNCTION LENGTH(FUNCTION UPPER-CASE(...))`, which only the
final version generates. Only seed 1 was run. An earlier run at 00:38Z, with the version of
`fntest_alnum.py` from before that statement was added, killed 13 of its programs (and the same 59
and 33 for the other two testers).

**06:17Z (re-run).** Tree `~/coblean_ifn_mutlive_20261027T0615Z`: a `cp -a` of live (equal to
snapshot `coblean-20261027T0518Z` except `HANDOFF_20261023.md`), with the three diffs applied by
`patch -p1` (no offsets), then `LRUN_AS=67108864 scripts/lrun.sh lake build cobolrun` (88 jobs).
Command, under `g.sh ifn_mutlive_tests1`, with `T` the tree:

    for t in num date alnum; do for s in 1 2; do
      python3 -I -B $T/tools/difftest/fntest_$t.py --root $T --out OUT/${t}_s$s \
          --n 60 --seed $s --show 1
    done; done

At seed 1 both the counts and the failing programs (case numbers) equal those of the 00:42Z run,
so there is no difference to explain.

## Variant: only 1700, 1800 and 1900 as leap years

```diff
--- a/Cobol/Sem/Arith.lean
+++ b/Cobol/Sem/Arith.lean
@@ -92,7 +92,7 @@
   else if x % 10 ^ s.toNat = 0 then some (x / 10 ^ s.toNat) else none
 
 /-- Gregorian leap year. -/
-def leapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
+def leapYear (y : Nat) : Bool := (y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)) || y == 1700 || y == 1800 || y == 1900
 
 /-- Days of month `m` (1-12) of year `y`. -/
 def monthDays (y m : Nat) : Nat :=
```

On a separate copy of live with only this patch (`~/coblean_ifn_mutleapv_20261027T0618Z`, same
build and command), `fntest_date.py` kills 28 programs at seed 1 and 18 at seed 2. That matches the
28 killed by the independent re-check's own leap-year mutant, if that run used seed 1; the fault as
planted (patch 2) kills 33 at seed 1.
