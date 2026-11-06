RESULT: CONFIRMED. The labelled NIST census N3 of coblean-20261028T0551Z reproduces exactly on an independently rebuilt tree: 309/309 per-program outcomes equal the producer's (pass 235, fail 11, unsupported 61, undefined 1, error 1, timeout 0; per test 5513 of 5570), the census output is byte-identical after path normalisation, and the recomputed transitions against N2 give the same 155 outcome changes (unsupported -> pass 131, error -> pass 14, fail -> pass 5, unsupported -> fail 3, error -> unsupported 2) and no pass -> non-pass. Two notes: (1) the first module job (NC, 07:00:22-07:00:42Z) ran before d0 recorded the pre-run summary (DEVIATIONS 07:01:04Z), although after the addendum (06:50:15Z) and after the summary file was written (06:59:57Z); (2) within N3 the declared switch setting decides pass versus fail for NC174A, NC211A and NC254A.

# NIST census N3 (labelled; plan prereg/ADDENDUM_NIST3_coblean.md 0a5fcca5, DEVIATIONS 06:50:15Z): evidence-owner check
An agent of the evidence-owner session, 2026-10-28 07:28Z-07:40Z (date -u). Check dir: this directory; replay dir ~/fv_paper/replay/nist3-20261028T072837Z
(tree = fresh cp -rL of the snapshot, 0 links; cln3m = my census run; switch_ctl; sysin_runner; sysin_cl). Read only on the COBOL maintainer session's files.

## 1. Sealed delivery: PASS
- ~/coblean_runs/nist3/sealed_20261028T072609Z: SHA256SUMS 729f32ff..., 2602/2602 OK, 0 writable files. DELIVERY_NOTE.md and
  COMMANDS.md read; tool hashes as in the pre-run summary (abend_status_v2 b5934936, mechanism_v3 fa2a9ba5, summarize_nist_v2 828eeb28).

## 2. Tree rebuilt independently: PASS (two expected differences)
- scripts/build_nist_n3_mine.sh: cp -rL of the snapshot, N2's D2 diff (192a4e0f, fuzz 0), cobolrun_files_v3.diff (d1406e94, fuzz 0),
  the NIST pin's tools/nist (equal to the pin), lake build cobolrun rc 0 (under my guard).
- Hashes equal to the producer's: cobolrun 195786db, tools/cobolfe/parser.py 74e35705, CobolRun.lean 05522fe7, run_nist.py 6635004c.
- Manifest (mine 05acb7c2, 2169 lines) vs the producer's tree_manifest_n3.sha256 (bf1403be, 2165 lines): differs only in (a) the 4
  symbolic links of third_party/gnucobol, which the producer's cp -a kept and my cp -rL turned into files, and (b) 5 lake metadata
  files (cobolrun.rsp, CobolRun.setup.json, CobolRun.trace, CobolRun.c.o.export.trace, cobolrun.trace), which are equal after the
  tree path is normalised (lake_meta_path_normalised.txt).

## 3. Census re-run: PASS
- scripts/census_mine.sh: NC SQ IX SM IC IF in order, each after the load/memory gate, frozen run_nist.py with COB_SWITCH_1=ON
  COB_SWITCH_2=OFF, no SYSIN, then abend_status_v2.py, mechanism_v3.py and summarize_nist_v2.py (07:30:40Z-07:33:11Z).
- Census text equal to the producer's final_census_n3.txt after replacing the run-directory paths (e8f80fb4 both;
  census_compare.txt). Per program, 309/309 final outcomes identical (outcomes_producer_vs_mine.diff empty); the six final.json files
  are identical after path normalisation (finaljson_compare.txt).
- Totals: pass 235, fail 11, unsupported 61, undefined 1, error 1, timeout 0; per test 5513 of 5570 (NC 3765/3822, SQ 515/515,
  IX 470/470, SM 275/275, IC 185/185, IF 303/303).

## 4. Transitions against N2 (nist_work/cln2), recomputed: PASS
- scripts/transitions_mine.py: 155 outcome changes, exactly the producer's breakdown; 0 pass -> non-pass.
- My row criterion (outcome, mechanism, normalised detail, matches, first difference) gives 169 rows: the producer's 168 plus NC175A,
  which fails in both runs with its first difference moved (87 -> 91 matches) and which the producer reports in its samefail
  supplement. On the 168 common rows the N2 and N3 outcome and mechanism equal the producer's table (transition_om_diff.txt empty).

## 5. Declared differences: PASS
- Runner: run_nist.py 6635004c in the NIST pin, in N2's tree (coblean-nist2-20261025T1848Z) and in mine.
- cobolrun_files_v3.diff vs N2's v2 (nist_work/d2/cobolrun_files_v2.diff 4e543ce3): the changed lines add OPTIONAL-file handling
  (absent optional files open with status 05; --absent), as declared (cobolrun_v2_vs_v3_changedlines.diff).
- Switch: a labelled control without COB_SWITCH (outside the census, my tree, same runner, --only): NC108M pass, NC174A fail,
  NC211A fail, NC254A fail; with the switch (census) all four pass (switch_control_summary.txt). In N2 all four were front-end
  rejections, so the setting changed no N2 outcome; within N3 it decides pass or fail for three programs.
- No SYSIN: NC109M unsupported, "ACCEPT: no system input device" (semantics-unsupported), as declared.

## 6. Attributions (sample of 14, against the before/after runs named in the evidence column): consistent
- scripts/attr_sample_mine_v2.py (attr_sample_v2.txt) and two hand checks: NC103A, NC244A (misc-fix 0327Z: unsupported -> pass);
  NC131A (index-fix, merge 2); NC207A (corr-fix, merge 5, stage and merge runs); NC214M (collate-fix, merge 3: merge-3 before ->
  after unsupported -> pass; the fix's own singles_after still unsupported, consistent with the row's "then ACCEPT FROM DAY in the
  same fix"); NC216A (c2-fix: N2 fail -> c2fix/cl pass); SQ121A, SQ212A, IX114A (decl-fix 0518Z); IX207A (fe-small leaves it
  unsupported, altkey-fix stage and merge 4 unsupported -> pass); SM103A (class-fix stage and merge 6, group SM103A+SM104A:
  unsupported -> pass); IC201A (nested-fix stage and merge 4); IF118A (ifn-fix 0245Z); NC109M (cobswait-fix: unsupported in both
  with the frozen runner, a mechanism change). The attributions remain the COBOL maintainer session's statements; this sample found no inconsistency.

## 7. Timing
- Plan fixed and logged before any run (DEVIATIONS 06:50:15Z). prerun_summary.txt written 06:59:57Z. Module jobs (guard logs):
  NC 07:00:22-07:00:42Z, SQ 07:01:03Z, IX 07:01:29Z, SM 07:01:54Z, IC 07:02:10Z, IF 07:02:31Z.
- d0's DEVIATIONS entry of 07:01:04Z says the summary was "received before any module run" and the switch scope "recorded before
  the runs"; both happened after the NC job had finished (and 1 s after SQ started). The producer disclosed the order. Since every
  outcome reproduces from the delivered commands, the order changes no result; the entry's wording should be corrected.

## 8. Separate labelled item, not part of the census: NC109M with run_nist_sysin.py: PASS
- ~/coblean_runs/nist3/sysin_sub/sealed_20261028T072806Z: SHA256SUMS 833a680b..., 166/166 OK, 0 writable.
- runner/tools/nist/run_nist_sysin.py 4c2cdede = merge 7's labelled runner; its diff against the frozen run_nist.py is one docstring
  line and the --sysin block (10 changed lines; sysin_runner_vs_frozen_mine.diff); parse_report.py f0b4b27e = the tree's.
- My re-run against my tree (--frontend and --cobolrun pointing at my tree, COB_SWITCH as in N3): NC109M pass, 11 of 11 GnuCOBOL
  entries matched, stop run; equal to the producer's.

## Compute: 0.019 guarded core-h over 33 guard logs (guard_totals.txt). Copies, hashing, diffs and jq/awk comparisons ran unguarded.
