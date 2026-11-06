# Addendum: labelled re-run of sample V at cirlean next3 (PIN), inputs fixed before the run

DRAFT v2 from cirlean (mutant) for the evidence owner, modelled on ADDENDUM_V_rerun_next2.md. PIN marks what the lead
fills in at the pin; nothing runs before the pin and before the evidence owner has recorded this.

Recorded by the evidence owner at PIN-UTC from cirlean's message; the output directory did not exist when this was
recorded. Not a pre-registration; a labelled re-check reported beside V (next revision).

- Sample: prereg/V/sample_V.tsv sha256 d0f38820db2e0f0516ea8262ec6c3b71dc1b04398dd14efa21a3206191dfeb94 (recomputed).
- Runner: ~/cirlean_work/llvmsub/tools/run_prereg_v10.py sha256 8150b519c92016f95b97a59c8a4516df0d7b39e5d258738acb460ff31990e815
  = run_prereg_v9.py (7b85c170...) with only these changes (diff run_prereg_v10.diff a6bcc154..., 4 hunks): a v10
  paragraph and the usage lines in the docstring; the cirrun binary is no longer a constant but --cirrun PATH, which
  must have the sha256 given as --cirrun-sha256, checked before the runner writes anything; --stop-utc is required
  (no default). So the runner is fixed before the pin, and the pin's binary is named only here. Smoke on the own mini
  corpus (llvmsub/smoke, 9 own programs, no row of V) with the 709db2e cirrun (8712d544...): 9/9 rows with the kind
  and sub of v9's smoke at next2 (~/cirlean_work/llvmsub/smoke/run10_709db2e, results.tsv eef1bcec...); a wrong
  --cirrun-sha256 stopped the runner with exit 1 before any output directory existed.
- cirrun: ~/cirlean_frozen/next3_PIN/.lake/build/bin/cirrun sha256 PIN (recomputed at the pin; passed to the runner
  as --cirrun and --cirrun-sha256); clang, gcc and the cirrun environment as in v7.
- Invocation as for runV_next2 (cores 120,123, global cap 1.40 core-h, an outer coreh_guard_v2 of 1.5 core-h), with
  --cirrun, --cirrun-sha256 and --stop-utc PIN added.
- next3 items in the pin: the first-parent commits of cirlean's next3 from next2 424e821 to the pin (recomputed at the
  pin; at f437da8 there are 56, with subjects in ~/cirlean_work/scratch/vnext3/next3_items_f437da8.tsv sha256
  50c5e17c50464531281cd23cff15cb2ba57f6e655ca1a3726ca7178e6a8c1908). The triage ties rows to these: retval (102, 131,
  196), vastruct in 4d7aaa3 (173), the bytes phases (52, 157), unionact3 (1, 123, 142, 144, 160; 139 in part; 179's
  site), and externglob2 (f437da8) gives the declared-only rule below. Pending when this was written, decided by the
  pin: intptr decides row 80; unionact4 (NX2) and nx3 (NX3) may change union and C++ rows (no row-level expectation).
- Output: ~/cirlean_work/llvmsub/runV_next3 (new). Delivery: sealed dir, results.tsv sha, per-kind counts against
  runV_next2 (813c52b6), runV_next_e6ac99a (e8f4129c) and runV (ac02a5a3), every changed row with old and new
  kind/sub, guard logs.
- Declared before the run, from the triage of runV_next2's 26 UB rows (~/cirlean_work/scratch/vtriage_next2,
  SHA256SUMS 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f; vtriage_next2.tsv 69bf80fd...;
  checked in evidence/checks/vtriage-20261028T190635Z):
  - The 11 false alarms next3 should fix are expected to be no longer UB at the triaged site (MATCH unless something
    later stops the run): 52, 102, 131, 173, 196 (marked yes in the triage: the byte rule for 52; retval for 102, 131
    and 196, each shown by a patched probe; vastruct for 173) and 1, 123, 142, 144, 157, 160 (likely: unionact for
    five, the byte difference of pointers for 157).
  - 139 (zerolen-1), partial: the union read is expected to pass and the GNU zero-length array read after it to stay
    UB ("invalid memory read" in the probe).
  - 80 (pr58209): with intptr in the pin, the int-to-pointer conversion has a flat address and the comparison is
    expected to change; without it, 80 stays UB ("unspecified pointer comparison").
  - The 13 real UB rows stay UB: 15, 25, 34, 36, 48, 51, 111, 127, 143, 158, 162, 179, 184. 179's message is expected
    to move from the union bit-field read at :50 (false at that site) to the left shift overflow at :71 (probe t179p).
  - Flag, row 158 (mayalias-1): cirlean's reason is the stride rule (pointer arithmetic out of bounds) and the ISO
    reason is 6.5p7 at the same expression; agreement there is with the verdict, not the reason.
  - Other rows: no row-level expectation; the delivery lists every changed row.
- Declared before the run: a faster cirrun can make a non-terminating program reach the 20 GiB address-space cap before
  the 120 s limit; such a row shows CRASH with resource=oom instead of TIMEOUT, and the delivery lists each one.
- Declared before the run: with externglob2 (in next3 since f437da8), a program that reads or writes a global it only
  declares, other than the modelled ones (stdin, stdout, stderr, the fundamental typeinfo objects,
  __libc_single_threaded), is UB ("external object without a model"); the delivery lists each such row.

Note for the evidence owner: evidence/checks/vtriage-20261028T190635Z/SUMMARY.md quotes the producer's SHA256SUMS as
3d300612...86a6c6. The file's sha256 is 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f (the head
matches; the file is unchanged since 2026-10-28T19:05Z, before that check); this addendum cites the full value.
