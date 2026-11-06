# copyrepltest.py: planted faults

Each mutant changes one place of `tools/cobolfe/textmanip.py` in a separate copy of `tools/cobolfe`
(the front end only: no Lean change, `cobolrun` is the tree's). The tester runs on the tree with the
copy's front end: `COBOLFE=<copy>/cobolfe.py python3 -I -B tools/difftest/copyrepltest.py --root .
--n 60 --seed 1 --out DIR` (`difftest.py` reads `COBOLFE`). The unmutated tree passes 60 of 60 at
seeds 1 and 2.

Recipe (one mutant at a time, on a fresh copy of `tools/cobolfe`): replace the exact text OLD, which
occurs exactly once in `textmanip.py`, by NEW.

| mutant | function | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|---|
| M1 | `apply` | the first replacement word always gets a space before it (no gluing to the text before the match: `S-:TAG:`, `X(5)` with `==5==`) | `out.append(x.moved(sp=(w.sp or pend) if k == 0 else x.sp, file=w.file, line=w.line,` | `out.append(x.moved(sp=True if k == 0 else x.sp, file=w.file, line=w.line,` | 20 of 60 fe-error |
| M2 | `expand_file` | REPLACE is processed before COPY (copied text escapes REPLACE) | `ws = replace_pass(copy_pass(ws, dirs, fmt, [os.path.abspath(path)], used, False))` | `ws = copy_pass(replace_pass(ws), dirs, fmt, [os.path.abspath(path)], used, False)` | 24 of 60 (10 mismatch, 14 fe-error) |
| M3 | `copy_pass` | a COPY statement's REPLACING phrase is applied before its copybook's own COPY statements are expanded (it misses the nested text) | the two statements `text = copy_pass(text, dirs, fmt, chain + [os.path.abspath(path)], used, replacing or bool(pairs))` and `if pairs: text = apply(text, pairs)` | the same two statements in the other order | 6 of 60 mismatch |

How the runs were made (2026-10-27): copies `~/coblean_runs/copyrepl/mut/M1..M3/cobolfe` (diffs
`mut/M*.diff`), runner `~/coblean_runs/copyrepl/tools/crt_v1.sh` with `COBOLFE` set, final tester
(sha256 `1e63e2ea...`): runs `mut_M*_s1c`, the same per-program statuses as the runs of the previous
tester version (`mut_M*_s1b`). M1 was detected in 5 of 60 programs before the tester had placeholders
glued to the text before them (`S-:TAG:`, `M-(TAG)-N`).

The unfixed tree (the snapshot `coblean-20261027T2008Z`, whose front end rejects `REPLACE`, `COPY ...
OF/IN` and operands of more than one token and does not glue replacements) gives, at seed 1, 56
`fe-error`, 2 `mismatch` and 2 `ok`, at seed 2 53 `fe-error` and 7 `ok` (the programs whose units
the old token-level `REPLACING` happens to handle).
