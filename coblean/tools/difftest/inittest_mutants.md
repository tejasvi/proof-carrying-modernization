# Planted faults and controls for `inittest.py`

`inittest.py` tests `INITIALIZE` of reference-modified identifiers and of identifiers with a
`REDEFINES` clause (README, the paragraph "`INITIALIZE` is tested by `inittest.py`"). This file
gives the controls on the resolver before the 2026-10-27 fix, the planted faults, the trees they
were applied to, the commands and the counts. Programs come from `random.Random(seed)`, 60 per
run with 20 statements each (the defaults), so a run is fixed by the tester's source, the seed,
`--forms` and the tree. All runs below used `inittest.py` sha256 `55ce687dba9ff6a4...` (2026-10-27);
every failure counted is a `mismatch` (a silent wrong result caught by the exact comparison)
unless marked `fe-unsupported`.

## The fix being tested

- `Cobol/Frontend/Resolve.lean`: `initTargets` no longer skips the identifier's own `REDEFINES`
  clause (IBM INITIALIZE rule 1a: "identifier-1 might itself have a REDEFINES clause"), only the
  items below it with or under one; `initRefMod` lowers a reference-modified identifier to one
  `MOVE SPACE` to the reference (IBM: "an elementary data item" of category alphanumeric), and
  to `unsupported` when data-name-1 is `COMP`, `COMP-3` or `COMP-5`.
- `tools/cobolfe/parser.py` (`ae_initialize`): the edited `MOVE SPACE` of alphanumeric-edited
  items is generated for the items of an identifier with a `REDEFINES` clause, and not for a
  reference-modified identifier (initialized unedited).

## Controls (the resolver before the fix)

Tree `~/coblean_init_ctl`: a `cp -a` of snapshot `coblean-20261027T0518Z` (13:42:17Z). Commands,
with `T=~/coblean_init/tools/difftest/inittest.py` (the tester is not in the snapshot):

    # C0: the 0518Z front end and cobolrun
    ~/coblean_runs/g.sh init_c0v4_s$s 0.2 python3 -I -B $T --root ~/coblean_init_ctl \
        --out ~/coblean_runs/init/c0v4_s$s --n 60 --seed $s --show 0
    # C1: the fixed front end, the 0518Z cobolrun
    COBOLFE=~/coblean_init/tools/cobolfe/cobolfe.py ~/coblean_runs/g.sh init_c1v4_s$s 0.2 \
        python3 -I -B $T --root ~/coblean_init_ctl --out ~/coblean_runs/init/c1v4_s$s \
        --n 60 --seed $s --show 0
    # per form, seed 1: --forms plain|redef|under|refmod (fixed tree: --root ~/coblean_init)

| Run | seed 1 | seed 2 |
|---|---|---|
| fixed tree (`--root ~/coblean_init`; rows V.init.s1, V.init.s2 of `make_evidence.py`) | 60 ok | 60 ok |
| C0 | 0 ok: 28 mismatch, 32 fe-unsupported | 0 ok: 24 mismatch, 36 fe-unsupported |
| C1 | 0 ok: 60 mismatch | 0 ok: 60 mismatch |

C0's `fe-unsupported` programs reference-modify an item with an alphanumeric-edited item inside,
which the 0518Z front end made unsupported because its resolver initialized the whole item.
The table's C0 and C1 runs are `g.sh init_c0v4_s$s` and `init_c1v4_s$s` (14:07Z, out
`c0v4_s$s`, `c1v4_s$s`); the same runs with the previous tester version (sha256 `0dd34f4e...`,
names `init_c0v3_*`, `init_c1v3_*`) gave byte-identical `results.jsonl` files.

Per form (C1 against the fixed tree, seed 1, sha256 `55ce687d...`): `plain` 60 ok / 60 ok,
`under` 60 ok / 60 ok, `redef` 0 ok (60 mismatch) / 60 ok, `refmod` 0 ok (60 mismatch) / 60 ok.

## The faults

Each fault is a one-line unified diff, applied from the tree root with `patch -p1` to a tree with
the fix. M1 and M2 change Lean sources, so `cobolrun` must be rebuilt
(`LRUN_AS=67108864 scripts/lrun.sh lake build cobolrun`: 88 jobs, about 15 s in a built copy).
The diffs are also in `~/coblean_runs/init/mutants/` (`m1_reflen.diff` sha256 `6a2d125f...`,
`m2_grouproot.diff` `e7fa1a82...`, `m3_ae_root.diff` `090e98c1...`).

### M1. The length of the reference is dropped

```diff
--- a/Cobol/Frontend/Resolve.lean
+++ b/Cobol/Frontend/Resolve.lean
@@ -311,7 +311,7 @@
 receives `SPACE`, whatever the items below data-name-1. Data-name-1 must have usage `DISPLAY`:
 a `COMP`, `COMP-3` or `COMP-5` item stops as unsupported. -/
 def initRefMod (ctx : Ctx) (d : Ref) : Except String (List Cobol.Stmt) := do
-  let r ← ref ctx d
+  let r ← ref ctx { d with refLen := none }
   match r.desc.kind with
   | .num f =>
     match f.usage with
```

`INITIALIZE A (s:l)` fills A from position s to its end.

### M2. Only an elementary identifier's own REDEFINES clause is ignored

```diff
--- a/Cobol/Frontend/Resolve.lean
+++ b/Cobol/Frontend/Resolve.lean
@@ -304,7 +304,7 @@
 /-- Elementary items an `INITIALIZE` of `it` sets. IBM rule 1a skips the items below `it`
 with or under a `REDEFINES` clause, but "identifier-1 might itself have a REDEFINES clause":
 the root's own clause does not count. -/
-def initTargets (it : Item) : List Item := initLeaves { it with redefines := none }
+def initTargets (it : Item) : List Item := initLeaves (if it.pic.isSome then { it with redefines := none } else it)
 
 /-- `INITIALIZE` of a reference-modified identifier. IBM: the reference is "an elementary data
 item" of category alphanumeric (data-name-1 of usage `DISPLAY`, a group included), so it
```

A group with a `REDEFINES` clause is skipped again (the fix half done).

### M3. The front end skips the edited moves of an identifier with a REDEFINES clause

```diff
--- a/tools/cobolfe/parser.py
+++ b/tools/cobolfe/parser.py
@@ -1324,7 +1324,7 @@
             return out
 
         def walk(e, occs):
-            if e.redefines is not None and e is not d.entry:
+            if e.redefines is not None:
                 return
             here = occs + ([e.occurs] if e.occurs is not None and e is not d.entry else [])
             if e.pic is not None:
```

The resolver initializes the alphanumeric-edited items of such an identifier with unedited
spaces, and the front end adds no edited `MOVE`: their `0` and `/` insertions are lost.

## Runs and kill counts

Trees `~/coblean_init_mut1`, `~/coblean_init_mut2`, `~/coblean_init_mut3`: `cp -a` of the fixed
scratch `~/coblean_init` (2026-10-27 13:52:34Z), each with its fault (the diffs above are `diff -u`
of the patched file against the scratch's; `patch -p1 --dry-run` applies each to the scratch);
`cobolrun` rebuilt in mut1 and mut2 (`g.sh init_mut1_build`, `init_mut2_build`, 88 jobs each).
Command (13:53-13:54Z):

    for m in 1 2 3; do for s in 1 2; do
      ~/coblean_runs/g.sh init_mut${m}_s$s 0.2 python3 -I -B $T --root ~/coblean_init_mut$m \
          --out ~/coblean_runs/init/mutants/m${m}_s$s --n 60 --seed $s --show 1
    done; done

| Fault | seed 1 | seed 2 |
|---|---|---|
| M1 length dropped | 60 of 60 | 58 of 60 |
| M2 group roots skipped | 53 of 60 | 53 of 60 |
| M3 front end, edited moves | 36 of 60 | 39 of 60 |

Unpatched (the fixed tree), both seeds agree on 60 of 60 programs (evidence rows V.init.s1,
V.init.s2).
