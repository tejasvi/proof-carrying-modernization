RESULT: coblean 1055Z re-check AGREES: manifest 305/305, sources differ from 2114Z only by the declared M-pos/C5 changes (+ testers/docs), TH0 from source 115 jobs 24 standard + 1 bv_decide (25 axiom lines identical to the 2114Z re-check), 95/95 re-run TSV rows match (incl. the 20 new rows exactly N), controls on the unfixed 2114Z reproduce (pos_check 11/20, fpos51 96/100); no discrepancy in any value.

# coblean live snapshot coblean-20261026T1055Z: evidence owner re-check (fork of the evidence-owner session)

Check dir: ~/fv_paper/evidence/checks/cob1055-20261026T2004Z; copies: ~/fv_paper/replay/cob1055-20261026T2004Z/{coblean, coblean_2114Z}.
Times UTC from date -u; work 20:04Z-21:20Z on 2026-10-26.

## Inputs
- Handoff ~/coblean_runs/handoff_to_paper_20261026.md: sha256 43d2a50c24e1d6ba6574ab9e80996fcd19b8d07ceb3078cbf313d77cc5a69b57 (= announced).
- Snapshot ~/coblean_snapshots/coblean-20261026T1055Z; manifest ~/coblean_runs/posfix/manifest_coblean-20261026T1055Z.sha256
  sha256 a49973cecfe1abe5a225d7981bc4a0b0a407dba8876fb19b7b0d5deaa682eedb (= announced), 305 entries (43 Cobol oleans + 262 other).
- TSV ~/coblean/docs/EVIDENCE_carddemo_live_20261026T1055Z.tsv sha256 3309d6485631fc022de14aa993c3418d15527e7bf95042cf0c39c2d5776c256c
  (= announced), 194 rows; identical to the snapshot's docs/ copy. Previous live TSV EVIDENCE_carddemo_live_20261025T2113Z.tsv f1aaa37d....

## 1. Manifest
- sha256sum -c in the snapshot: 305/305 OK (manifest_check.txt); again 305/305 after all runs.
- Full copy (cp -a) into replay/.../coblean: diff -rq against the snapshot empty before and after the runs; 4 symlinks, all relative
  and inside third_party/gnucobol; no absolute symlink.
- Live ~/coblean now differs from the snapshot only in HANDOFF_20261023.md (diff_snapshot_vs_live_now.txt).

## 2. Diff against coblean-20261025T2114Z (the snapshot re-checked 2026-10-25T21:44Z; diff_2114Z_1055Z.txt, 143 lines)
- Lean sources: Cobol/IR.lean (+6: field FileSt.bound : Option (List UInt8 x Bool) := none), Cobol/Sem/File.lean (+45/-3: new defs
  boundAt and afterBound; fileOpen, fileRead (both READ forms), WRITE and fileStart gain an `if d.access == .dynamic` branch; each
  else-branch is the old code, one comment reworded), Cobol/Logic/Eval.lean (+1/-1: the cobol_eval attribute list gains Sem.boundAt
  and Sem.afterBound). Python: tools/cobolfe/parser.py (+11/-5, C5: record area = first largest 01; 01s of different lengths without a
  RECORD clause give minLen/maxLen = shortest/longest; the former "unsupported" line for that case removed) and its .pyc;
  tools/evidence/make_evidence.py (+23: the 20 new rows). Docs: README.md, HANDOFF_20261023.md, new docs/COV_REPORT.md (5c817809...
  = the report recorded 09:20Z) and the new TSV. New testers: tools/difftest/{pos_check.py, filetest2_pos.py, c5_check.py,
  ext_common.py, c5_cases/, cov/} (cov/ = ~/coblean_cov/tools/difftest/cov apart from the scratch-only probe files).
- My per-file diffs equal ~/coblean_runs/posfix/diffs_live and diffs_final (bodies after the two header lines, all 5 files);
  diffs_live and diffs_final are byte-identical (src_diff_*.diff).
- Build products: 3 Cobol oleans (IR, Logic/Eval, Sem/File) and 19 Examples theorem-module oleans differ from 2114Z (rebuilt against
  the changed library; the Examples oleans are not in the manifest); their statements and axioms are covered by TH*.st/TH*.ax and TH0.
- Note: Logic/Eval.lean is a source change of the M-pos set (it is in diffs_live and in coblean's olean sentence, but the 10:56Z
  message's M-pos sentence names only IR.lean and File.lean).

## 3. TH0, oleans, IRs
- TH0 (tools/cob_evidence_run.py, recheck_build.sh unchanged from 2114Z, one CPU, LEAN_NUM_THREADS=1): rc 0, 1,600 s, "Build completed
  successfully (115 jobs). | standard: 24 | bv_decide: 1" = expected; 0 error lines; the 25 axiom lines (th0_axiom_lines.txt) are
  identical to my 2114Z TH0 re-check (cobE5-20261025T2117Z); the one bv_decide line is bincnt_equiv (BINCNT example).
- Cobol.olean be3132eb... (unchanged). The 43 Cobol oleans against coblean-20261024T2306Z: 5 differ (Edit, IR, Layout, Logic/Eval,
  Sem/File), 38 identical (oleans_vs_2306Z.txt) = coblean's statement.
- The 9 CardDemo IRs (examples/carddemo/*.ir.json) are byte-identical to 2306Z's (carddemo_irs_vs_2306Z.txt).

## 4. TSV rows re-run (results/*.json; command file all_cmds.txt; pjobs.log)
- Against f1aaa37d: all 174 old rows differ in the checked_utc column only, except T4, E4, T7 (value and expected): 171 identical
  apart from check times, 3 line counts, 20 new rows (tsv_compare.txt).
- Re-run from my copy with tools/cob_evidence_run.py (95 rows, each under coreh_guard_v2, ulimit -v 32 GiB, one CPU via taskset,
  PYTHONDONTWRITEBYTECODE=1): TH0 1/1, TH*.ax 25/25, TH*.st 25/25, IR.* 11/11, IRFE.* 9/9 (front end output = shipped IR after key
  sorting, with the C5 parser), IRB.examples 1/1, T4 3128, E4 6666, T7 3234 (all = expected), and the 20 new rows exactly as
  expected: V.pos {"ok":20}, V.fpos51 {"ok":100}, V.fpos52 {"ok":100}, V.c5 {"ok":3}, V.cov.{f1inp, f1multi, f2vary, f3round,
  f3prohib, f4lit, f4items, f5str}.s{1,2} {"ok":60} each, every one "N cases, tester exit 0".
- Writes reviewed before the run: every new tester writes only under its --out dir in $OUT (cobc output, data files, fe.json),
  cobc temporaries under TMPDIR=$OUT/tmp; the copies were unchanged after the runs (diff -rq empty).
- Controls on a fresh copy of the unfixed 2114Z (replay/.../coblean_2114Z, diff -rq = snapshot before and after), with the 1055Z
  testers: pos_check 11 of 20 agree, rc 1 (control/pos_2114Z.log); filetest2_pos seed 51: {"ok": 96, "mismatch": 4}
  (control/fpos51_2114Z.log). Both = coblean's recorded controls.

## 5. NIST C1 and C2; INSPECT on theorem paths
- C1 (IBM Enterprise COBOL 6.4, "SIZE ERROR phrases", read with WebFetch): "If the ON SIZE ERROR phrase is not specified and a size
  error condition occurs, truncation rules apply and the value of the affected resultant identifier is computed." and "If the NOT ON
  SIZE ERROR phrase has been specified and, after execution of an arithmetic operation, a size error condition does not exist, the
  NOT ON SIZE ERROR phrase is executed." Supports class (iii) as suggested (coblean truncates, as IBM states).
- C2 (IBM Enterprise COBOL 6.4, "INSPECT statement", Table 1 row for signed zoned decimal items; the tool returned excerpts only,
  a second fetch for the full row failed with a tool-side error): "As if moved to an unsigned external decimal item of usage DISPLAY
  with the same length as the identifier", "redefined as category alphanumeric", and "If the sign is a separate character, the byte
  containing the sign is not examined and, therefore, not replaced." Supports class (ii) as suggested (coblean inspects the stored
  bytes with the overpunch).
- INSPECT scan: the 15 IR files the theorems load (9 CardDemo incl. cbstm03ab, acctint x2, bincnt x2, recsum x2) contain 0 "inspect"
  and 0 "convert" statement tags (inspect_scan_ir_v2.txt); positive control: the front end on tools/difftest/inspect_cases/insp1.cob
  emits 18 "inspect" and 2 "convert" tags (inspect_ctl/). The 11 theorem program sources (CBACT01C-04C, CBCUS01C, CBTRN01C-03C,
  ACCTINT, BINCNT, RECSUM) have 0 non-comment lines with the INSPECT verb (inspect_scan_src.txt).

## Not checked here
- The NIST singles on the 14 C5 programs (8 pass, 5 unsupported, 1 error; outside the measured runs), the cov mutant-plant controls
  of COV_REPORT.md, and the R4 fallback (i) probe figures.

## Compute and slips
- 0.800 core-h for the 96-job run (outer guard, guard_outer.log) + 0.129 core-h (TH25.ax re-run, fpos51 control) = 0.929 core-h.
- TH25.ax's first run was stopped by my own per-job cap (0.05 core-h; rc 137, no result written); re-run alone with cap 0.3:
  rc 0, match, 449 s (rerun_TH25ax/results/TH25.ax.json).
- Slip: one empty file (copy-identity diff output) was written in ~/fv_paper/replay/ next to my dir at 20:06Z and moved into this
  check dir (copy_identity_diff.txt) within a minute.

## Questions for producers
- None blocking.
