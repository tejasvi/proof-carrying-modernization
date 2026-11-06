# Addendum: C1 attribution run of the NIST census N3 (coblean; exploratory; recorded 2026-10-28T10:44:58Z, before the run)
Not a pre-registration: an exploratory check that the remaining N3 failures (other than NC107A) come from the
size-error rule C1 (the semantics follows IBM: without ON SIZE ERROR, a size error stores the truncated result).
Plan sent by the COBOL maintainer session at about 10:44Z; nothing runs before this record.

1. Variant tree = the N3 tree recipe (snapshot 20261028T0551Z + N2's D2 diff 192a4e0f + cobolrun_files_v3.diff d1406e94
   + the pin's tools/nist, built as by build_nist3_v1.sh 14e37d1f; N3 tree manifest bf1403be) plus one change before the
   build: ~/coblean_runs/c1var/patch/c1var_resolve.diff, sha256 b740d599fe6a7399645530c3e956b9d54328a4464d79f7f443c3d99046103326
   (verified by us: b740d599fe6a7399). File Cobol/Frontend/Resolve.lean (3be4dbc0 -> dd5de241): at lines 519 (COMPUTE),
   527 (ADD), 537 (SUBTRACT), 544 (MULTIPLY), 554 (DIVIDE REMAINDER), 557 (DIVIDE) the trap flag onSize.isSome becomes
   (onSize.isSome || !notOnSize.isEmpty): a size error leaves the receiver unchanged whenever either SIZE ERROR phrase is
   present (also each pair statement of ADD/SUBTRACT CORRESPONDING). Front end and its output unchanged. The built tree's
   manifest and its diff against bf1403be are sent before the run (expected: Resolve.lean plus build outputs only).
2. Runner: the frozen N3 runner, unchanged (N3 COMMANDS.md s3-4): tools/nist/run_nist.py 6635004c, env COB_SWITCH_1=ON
   COB_SWITCH_2=OFF, inputs nist_work/extract5 (manifest.json f639c71d) and gc4 (hashes as in N3's inputs_frozen_hashes.txt),
   then abend_status_v2 b5934936, mechanism_v3 fa2a9ba5, summarize_nist_v2 828eeb28; one module at a time, same load gate.
3. Run list: all 309 programs of NC SQ IX SM IC IF (95/85/42/17/25/45), the N3 census set:
   ~/coblean_runs/c1var/pre/runlist_309.tsv (sha256 prefix verified by us 5d9c36ab6a4939f1); N3 outcomes
   runlist_n3_outcomes.tsv (a86e2999f3363025).
4. Expected outcome against sealed N3, per test entry: exactly the 55 FAIL entries of
   ~/coblean_runs/c1var/pre/expected_flips_55.tsv (07e07032f3306343) become PASS (NC106A 2, NC170A 7, NC171A 7, NC172A 8,
   NC173A 8, NC175A 6, NC176A 7, NC177A 7, NC202A 2, NC253A 1; these 10 programs fail -> pass); NC107A stays fail
   (JUST-TEST-04 x2); no other test entry, program outcome, kind or mechanism changes in any module. Census: pass 235 ->
   245, fail 11 -> 1; unsupported 61, error 1, undefined 1 unchanged. NC per test: 3765 -> 3820 of 3822 GnuCOBOL entries
   matched; NC grading PASS 3741 -> 3796, FAIL 57 -> 2. Any other difference counts against the attribution and is
   reported as found.
Runs by the session's helper under ~/coblean_runs/c1var (new dir); ~/coblean_runs/nist3 untouched.
Our check afterwards: compare per-test outcomes with sealed N3 and re-run a sample, as for N3.
