RESULT: the IBM-variant repeat on coblean 20261027T2008Z (sealed_20261027T2044Z) CHECKS OUT: seal and design as recorded before the run; table recomputed; 12 of 66 runs re-run from a copy reproduce every output byte for byte; every non-agreement class checked on samples is a GnuCOBOL departure from IBM, a translation artifact or a decline, with no model defect found; the planted front-end control did not exercise its sign table.

# An agent (fork of the evidence-owner session), written 2026-10-28T00:07:35Z (date -u)
Inputs: ~/coblean_runs/ibmvar/live/sealed_20261027T2044Z (read-only), raw runs ~/coblean_runs/ibmvar/live/runs, pre-run list in
prerun/. Copies: ~/fv_paper/replay/ibmvar2-20261027T2355Z/{tree (cp -a of ~/coblean_snapshots/coblean-20261027T2008Z; 4 relative
links inside third_party/gnucobol), shadow (cp -a of the producer's shadow; third_party re-pointed to my tree), table, plant_fe,
runs, guard}. Producer files only read; the producer's bin/ wrappers executed read-only from their path.

1 PASS seal: SHA256SUMS 6106f876..., 438/438 OK, 439 files, 0 writable, 0 symlinks (seal_check.out); RUNS_MANIFEST.sha256 46499/46499
  OK on live/runs, 0 writable, 0 links (runs_manifest_check.out); the 74 sealed run dirs = the raw run dirs.
2 PASS design: prerun/PRERUN_LIST_live_v1.txt sha256 1e3625d2... = the hash in prereg/DEVIATIONS.md (2026-10-27T20:22:19Z, before any
  tester run; runs started 20:23:02Z per LIVE_PROGRESS). Wrapper and job-list hashes = the list (cobc e4a59284, fe 67a7c31b,
  cobolrun wrapper e7ed24f6, layout 1b43a873, launcher 03393f4f, lane e82219ee, jobs A cfc493c6, B 054bc2a0, scanner 5eb0fc51,
  shadow builder 36d95bdc; shim c96c5afa); table a99f6bfb; shadow tools/difftest (448 files) byte-identical to the 2008Z
  snapshot's; snapshot cobolrun 1a0a80d1 = the list's (the producer's tree copy no longer has its build; I used the snapshot's).
  Deviations as logged: D-L1 (cf1inp_s1 crashed: shadow lacked tools/irjson.py; a byte-identical copy added mid-run; rerun
  cf1inp_s1_r2), D-L2 (c5check, poscheck crashed on an existing out dir; reruns _r2). The summarizer (v3) is a post-run tool; the
  second-verdict rule it applies is item 9 of the pre-run list.
3 PASS recount: tables/PROGRAMS.jsonl 4105 programs; per-run class counts = tables/TABLE.txt for all 71 runs with programs (plus 3
  zero-program rows of the crashed first attempts) (recount_from_programs.txt, table_txt_counts.txt); per-program status =
  runs/*/results.jsonl for 4105/4105 (programs_status.tsv = results_status.tsv). The 66 seeded runs (3,960 programs): 3,252 agree,
  11 declined, 50 unflagged mismatch, 647 flagged; by final verdict: 3,391 agree (incl. 139 flagged with an ok status), 264 agree
  after the relaxed comparison, 120 agree up to class Z, 63 twin-raw-equal, 34 declined (11 PERFORM forms; colltest 14 STANDARD-1/2
  and 9 alphabets naming a character twice in EBCDIC), 88 still differ (colltest 81 explicit collating sequences, aetest 7
  HIGH-VALUE ordering).
4 PASS re-runs (scripts/my_lane.sh = the producer's lane logic with my dirs and coreh_guard_v2 per job; same tester args): insp_s1,
  dtstd_s1, initrepl_s1, init_s1, ae_s1, cf5str_s1, ctrl_s1, initptr_s1, coll_s1, cf4items_s1, ctlW_insp_s1, ctlA_dtstd_s1:
  results.jsonl byte-identical 12/12; tester stdout identical (coll_s1 after normalising the run path in 3 messages); GnuCOBOL
  outputs 720/720 identical; cobolrun raw and translated outputs identical by name (rerun_cmp.txt). Guard total 0.051 core-h.
5 PASS classes (samples):
  H  HIGH-VALUE byte: dtstd_s1 T00026, model raw storage holds 5 bytes 0xFF = GnuCOBOL's; translated 0x9F.
  HO HIGH-VALUE ordering: probe/hvord.cob with the same GnuCOBOL flags and table: HIGH-VALUE > 'RRR', < 'SSS', < 'YYY', < '999'
     (GnuCOBOL places it at X'DF'); IBM's X'FF' is the highest character; aetest ae_1_9 C15 (HIGH-VALUE > 'Y7-P348FK'): GnuCOBOL N,
     model Y = IBM.
  Z  init_s1 p1_0000: exactly 3 differing bytes, each GnuCOBOL '0' against the model's X'C0' in a signed zoned item after
     INITIALIZE (G3G S9(2), G1C S9(1)V9). IBM rule read from the local text of the IBM 6.4 Programming Guide (igy6pg40.txt lines
     4501-4532 "Signed positive or 0: X'C'"; 23283-23302 "signed overpunch: ... X'C' if a number is positive or 0"; PDF sha256
     b821f73d...): the model's C is IBM's, GnuCOBOL's F is the departure.
  C/rawview  initrepl_s1 first differences: character fill in COMP storage (model 0x7B, EBCDIC '#', against GnuCOBOL 0x23; equal
     after the table) and binary bytes in character positions (equal raw: 0xEF, 0x23, 0x4F); consistent with the class.
  1b twin-raw-equal  initptr_s1: raw model storage of P and T byte-identical in 59/60 cases, including all 29 claimed; the one
     raw-different case (43) is classed twin-mismatch-storage, not raw-equal.
  K  coll_s1 p1_0003 S00: N1=509 against A3='T' under a literal alphabet that lists neither character; unlisted characters follow
     the native order: EBCDIC 'T' (X'E3') < '5' (X'F5'), so the condition is false and the model prints N, IBM's result; GnuCOBOL
     uses ASCII order ('5' < 'T') and prints Y. p1_0001: THRU ranges run in the native order.
  KD coll_s1 p1_0004: ALPHABET '@' THROUGH '<' covers '&' (X'50') in EBCDIC and '&' is listed again: invalid under IBM; the model
     rejects it ("a character is given more than once"); p1_0012/19/20 STANDARD-1/2 refused by the IBM profile.
  Declines  ctrl_s1 C00000: PERFORM P2 THRU P6 executed inside the active range P0 THRU P6 (lean-unsupported-recursion), as in 2306Z.
  Caveat: the relaxed second verdict accepts a byte when it matches by either view (table or raw), so inside flagged programs a
  character stored in the wrong code would pass when its raw byte equals GnuCOBOL's; the field-aware first verdict has no such
  allowance. The classes above were checked on samples, not on every program.
6 controls and coverage: CTL-W-live reproduced (60/60 mismatch, only from the planted table). CTL-A-live reproduced in the same form:
  59 frontend-cobolrun-error (the cobolrun wrapper refuses the planted IR's configuration, exit 97) + 1 HIGH-VALUE mismatch, so the
  planted sign table never ran: this repeat has no working front-end sign control (the 2306Z run's control caught its 23 cases).
  COVERAGE_NOTES: INITIALIZE (CBACT01C, CBTRN02C, CBTRN03C, CBSTM03A) and CBACT01C's variable-length output records are now
  compared under the IBM variant (cov_f2vary 120/120 agree); still untested: the 7 DISPSIGN(COMPAT) operands, EBCDIC record-key
  order, the clock (CBACT04C, CBTRN02C), CBACT01C's COBDATFT call, CBTRN03C's exact edited pictures, CBSTM03A's address-space walk;
  the CardDemo extra E1 (CBSTM03A with CBSTM03B on sample data) was not repeated.
7 Proposed paper text (sec-limits, after the first IBM-variant run; labelled): see the final message of this check.
