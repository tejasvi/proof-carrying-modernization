# Addendum: labelled re-run of sample V at cirlean next3 (7c73739), inputs fixed before the run

FINAL from cirlean (mutant) for the evidence owner, sent at 2026-10-30T02:37:52Z (PIN-UTC), modelled on
ADDENDUM_V_rerun_next2.md; RECORD-UTC below is the evidence owner's. Nothing runs before the evidence owner has
recorded this.

Recorded by the evidence owner at 2026-10-30T02:39:24Z from cirlean's message; the output directory did not exist when this was
recorded. Not a pre-registration; a labelled re-check reported beside V (next revision).

- Pin: cirlean next3 7c73739c0cb655d07f4a452cc3317cafb2b1bcb4 (next3 50e88b0 plus CHANGES_next3.md and
  RESTATEMENTS_next3.md), frozen tree ~/cirlean_frozen/next3_7c73739_20261030, build manifest
  scratch/next3_chain/freeze_next3_7c73739/MANIFEST_build.sha256 (1017 files) sha256
  8d2cc1ff96e4b41ae950ddc3e328b93c79bf0ec9fff7b9857262a848dba1352f.
- Sample: prereg/V/sample_V.tsv sha256 d0f38820db2e0f0516ea8262ec6c3b71dc1b04398dd14efa21a3206191dfeb94 (recomputed).
- Runner: ~/cirlean_work/llvmsub/tools/run_prereg_v10.py sha256
  8150b519c92016f95b97a59c8a4516df0d7b39e5d258738acb460ff31990e815 = run_prereg_v9.py (7b85c170...) with only these
  changes (diff run_prereg_v10.diff a6bcc154..., 4 hunks): a v10 paragraph and the usage lines in the docstring; the
  cirrun binary is no longer a constant but --cirrun PATH, which must have the sha256 given as --cirrun-sha256, checked
  before the runner writes anything; --stop-utc is required (no default). Smoke on the own mini corpus (llvmsub/smoke,
  9 own programs, no row of V) with the 709db2e cirrun (8712d544...): 9/9 rows with the kind and sub of v9's smoke at
  next2 (~/cirlean_work/llvmsub/smoke/run10_709db2e, results.tsv eef1bcec...); a wrong --cirrun-sha256 stopped the
  runner with exit 1 before any output directory existed.
- cirrun: ~/cirlean_frozen/next3_7c73739_20261030/.lake/build/bin/cirrun sha256
  2995b7945381822e300cfccf98cc7a7802bb8612b0904d45ddbc3ddab6cf8101 (recomputed when this was written;
  passed to the runner as --cirrun and --cirrun-sha256); clang, gcc and the cirrun environment as in v7.
- Invocation as for runV_next2 (cores 120,123, global cap 1.40 core-h, an outer coreh_guard_v2 of 1.5 core-h), with
  --cirrun and --cirrun-sha256 as above and --stop-utc 2026-10-31T02:00:00Z.
- next3 items in the pin: the 88 first-parent commits of cirlean's next3 from next2 424e821 to 7c73739, with subjects
  in ~/cirlean_work/scratch/vnext3/next3_items_7c73739c.tsv sha256
  118f84ae7b828ef0ea9133e350d9cebdf2013481062241bef6d93fa54ae40447. The triage ties rows to these:
  retval (102, 131, 196), vastruct in 4d7aaa3 (173), the bytes phases (52, 157), unionact3 to unionact5b (1, 123, 142,
  144, 160; 139 in part; 179's site), intptr2 (80); externglob2, externglob3 and its EG1 commit give the declared-only
  rule below.
- Output: ~/cirlean_work/llvmsub/runV_next3 (new). Delivery: sealed dir, results.tsv sha, per-kind counts against
  runV_next2 (813c52b6), runV_next_e6ac99a (e8f4129c) and runV (ac02a5a3), every changed row with old and new
  kind/sub, guard logs.
- Declared before the run, from the triage of runV_next2's 26 UB rows (~/cirlean_work/scratch/vtriage_next2,
  SHA256SUMS 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f; vtriage_next2.tsv 69bf80fd...;
  checked in evidence/checks/vtriage-20261028T190635Z):
  - The 11 false alarms next3 should fix are expected to be no longer UB at the triaged site (MATCH unless something
    later stops the run): 52, 102, 131, 173, 196 (marked yes in the triage: the byte rule for 52; retval for 102, 131
    and 196, each shown by a patched probe; vastruct for 173) and 1, 123, 142, 144, 160, 157 (likely: unionact for
    five, the byte difference of pointers for 157).
  - 80 (pr58209), a false alarm with no fix at the triage: intptr2 gives the integer-to-pointer conversion a flat
    address with the provenance of the live block, and the census's pr58209 returns 0 from main (as 11 other census
    programs with integer/pointer casts do), so 80 is expected no longer UB (MATCH unless something later stops it).
  - 139 (zerolen-1), partial: the union read is expected to pass and the GNU zero-length array read after it to stay
    UB ("invalid memory read" in the probe).
  - The 13 real UB rows stay UB: 15, 25, 34, 36, 48, 51, 111, 127, 143, 158, 162, 179, 184. 179's message is expected
    to move from the union bit-field read at :50 (false at that site) to the left shift overflow at :71 (probe t179p).
    48, 127 and 184 ran through the runner's harness at next2 (main with parameters); with gaps6 cirrun gives main its
    argc = 1 itself, so the runner is expected to run their main directly (harness 0, the sub without "harness:").
  - Flag, row 158 (mayalias-1): cirlean's reason is the stride rule (pointer arithmetic out of bounds) and the ISO
    reason is 6.5p7 at the same expression; agreement there is with the verdict, not the reason.
  - Other rows: no row-level expectation; the delivery lists every changed row. Kinds of change the items can bring:
    - rows that used the harness at next2 run main directly (gaps6: main(int) and main(int, char **) get argc = 1);
    - TIMEOUT rows may finish (perf1, perf2: long loops in linear time);
    - UNSUPPORTED rows may run further: gaps1-5 and gaps7 (inline asm with memory operands for empty templates and
      register-to-memory moves, strncpy, strcat, strrchr, SSE intrinsics, __builtin_setjmp, libc++'s hash,
      std::string::reserve, fread, fscanf and ungetc(EOF) on the empty stdin, fputs and fwrite results, the ffs family,
      lrand48 and seed48, map/set/list copies), t2models8 (errno readable after the C library's models, strerror_r,
      time, ctime_r, perror), arrnew/arrfix (new T[n] of a class with a constructor);
    - C++ rows may change where empty members overlap others (gaps7 drops the stores and copies of types with no value
      representation) and union rows where a member of another size, a _Bool or a character member is read
      (unionact4b, unionact5b, unionfix3);
    - a row may become UB where a program uses an object after its destructor started (nx3), writes a const local
      after its initialization (constobj3), converts a pointer to an ended object to an integer (intptrzap), lets
      vector code access another type's object (vecstore), passes atof an overflowing value (t2models8), or meets one
      of auditfix8's checks (setjmp contexts, va_list ownership, literal printf formats).
- Declared before the run: a faster cirrun can make a non-terminating program reach the 20 GiB address-space cap before
  the 120 s limit; such a row shows CRASH with resource=oom instead of TIMEOUT, and the delivery lists each one.
- Declared before the run: with externglob2 and externglob3 (in next3 since f437da8, 19fdd46 and edcea40), a program
  that reads or writes a global it only declares is UB ("external object without a model"; "invalid memory read" for
  a constant one) unless it is modelled: stdin, stdout, stderr, the fundamental typeinfo objects,
  __libc_single_threaded (1), getopt's optind and opterr (1 at the start), libm's signgam (the sign lgamma stores) and
  the C++ standard stream objects (live, of indeterminate value: a read of a member is UB). environ and
  program_invocation_name are not modelled. The delivery lists each such row.

Note for the evidence owner: evidence/checks/vtriage-20261028T190635Z/SUMMARY.md:7 quotes the producer's SHA256SUMS
as 3d300612...86a6c6. The file's sha256 is 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f (the head
matches; the file is unchanged since 2026-10-28T19:05Z, before that check); this addendum cites the full value.

Evidence owner's check at recording (2026-10-30T02:39:24Z): the FINAL file received (~/cirlean_work/scratch/vnext3/ADDENDUM_V_rerun_next3_FINAL.md)
has sha256 8b417d57320d7605fc0139edd137782d3d878c978035373cb1379fe1a984714d, as announced; this record differs from it only in
the RECORD-UTC filled above and this paragraph. Recomputed: sample_V.tsv d0f38820...; run_prereg_v10.py 8150b519...; cirrun
2995b794... (= the frozen manifest's entry; manifest 1017/1017 OK, HEAD 7c73739, 0 tracked changes:
evidence/checks/next3pin-20261030T023649Z); next3_items_7c73739c.tsv 118f84ae... (88 rows), and git rev-list --first-parent
--count 424e821..7c73739 = 88; the output directory ~/cirlean_work/llvmsub/runV_next3 did not exist. Diff against the recorded
draft v2 (33e1057a): pin fields, the item list, the expectation for row 80, rows 48/127/184 (main with argc = 1), the kinds of
change since draft v2, and the extended declared-only rule.
