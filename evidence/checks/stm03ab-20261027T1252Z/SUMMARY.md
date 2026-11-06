RESULT: CBSTM03A with CBSTM03B linked checks out. The snapshot is 2306Z plus exactly the stated additions (the 43 Cobol oleans identical, Cobol.olean be3132eb); the linked IR regenerates byte for byte from the unmodified sources; all 28 new modules compile from source in my copy; stm_run_sorted, stm_run, stm_run_abort_cust and stm_run_abort_acct each print exactly [propext, Classical.choice, Quot.sound]; the 71-module closure (43 Cobol + 28 new) replays rc 0 (controls as expected); the GnuCOBOL differential agrees (1212 and 6082 records, 0 differ); the theorem's 11 walk lines are the 11 lines the differential skips.

# CBSTM03A+B all-input theorems (checks/stm03ab-20261027T1252Z; copy replay/stm03ab-20261027T1252Z; written 2026-10-27T13:12Z by date -u)

## Copy and identity
- cp -rL of ~/coblean_snapshots/coblean-pin2306Z-cbstm03ab-20261027T1251Z (690M): 0 symlinks; diff -rq copy vs snapshot empty
  (copy_identity.txt).
- diff -rq coblean-20261024T2306Z vs snapshot, excluding .lake and third_party: only Examples/Stm/, Examples/StmCore/,
  STMCORE_PROGRESS.md and lakefile.toml (diff_2306Z_vs_snapshot_src.txt). lakefile.toml (3b86eb31) adds one lean_lib StmCore,
  globs Examples.StmCore.+ and Examples.Stm.+ (lakefile_diff.txt). third_party identical. In .lake only Examples/Stm and
  Examples/StmCore build outputs are new; all 43 Cobol oleans identical to 2306Z; Cobol.olean be3132eb.
- ~/coblean_runs/stmcore2/final_sha256.txt (600021685c916f3c, 22 lines: 21 StmCore files + WalkSummary): 22/22 OK against the
  snapshot (final_sha256_check.txt).

## Linked IR (regen/)
- CardDemo 59cc6c2f (~/veriforch/targets/carddemo_src/carddemo; no promisor, no partial clone; git read-only with
  GIT_ALLOW_PROTOCOL=file): CBSTM03A.CBL 23c8753b, CBSTM03B.CBL ac004f7f, the 30 copybooks (each the HEAD blob).
- scripts/regen_ir.sh (coblean's IRFE.cbstm03ab recipe): cobolfe.py on each source (--tab-width 4), link.py a b -> ab.json =
  examples/carddemo/cbstm03ab.ir.json byte for byte (2c5ba72b...), also equal after key sorting; = 2306Z's file.
- Abend code: CBSTM03A.CBL:923 is "CALL 'CEE3ABD'." with no USING (9999-ABEND-PROGRAM, after DISPLAY 'ABENDING PROGRAM'); the
  other CardDemo programs pass a code (CBACT01C.cbl:410 USING ABCODE, TIMING). The front end (tools/cobolfe/parser.py:1538-1542)
  emits code {"lit":{"v":-1,"scale":0}} when CEE3ABD has no argument ("without arguments the code is unspecified: -1"); the IR's
  only abend node is {"code":{"lit":{"v":-1,"scale":0}}}. In the model, Cobol.IR.lean:458-459 documents Fault.abend (code : Int)
  "-1: none given", and Sem/Exec.lean:537-540 evaluates the code expression and ends with .fault (.abend k). So -1 is the model's
  marker for an abend without a user code, not an IBM abend code (regen/abend_frontend_and_model.txt, cbstm03a_abend_lines.txt).

## Build from source, axioms
- scripts/compile_stmcore.sh: the copy's prebuilt Examples/Stm and Examples/StmCore oleans moved aside (in my copy); the 28
  modules compiled one at a time in dependency order (compile_order.txt, from imports.txt) with lean v4.35.0 and the lakefile's
  leanOptions into my out/lib: 28/28 rc 0 (logs/compile_all.tsv; longest Mainline2 78 s). Messages are linter warnings only
  (unused variables, one deprecation); no error and no "declaration uses 'sorry'".
- Fresh process (scripts/check_thms.sh, logs/check_thms.out): the four theorems each depend on exactly [propext,
  Classical.choice, Quot.sound]; #check of each printed with its hypotheses.
- The theorems are about the semantics' interpreter: Stm is the Cobol.Program defined by cobol_program from
  examples/carddemo/cbstm03ab.ir.json (Examples/Stm/WalkSummary.lean:23), Stm.run = Cobol.Program.run = Sem.runFrom from
  paragraph 0, Stm.initState m0 inp = { mem := Stm.initMem m0, inp := inp } (logs/check_defs.out).

## Statements in words
stm_run_sorted (Sorted.lean): for every environment env and storage m0, if
- env.addrSpace = Stm.asp (the fixed bytes of the z/OS PSA, TCB and TIOT that the program's control-block walk reads: job
  CREASTMT, step STEP040, nine DD entries) and env.openError f md = none for all f, md (every OPEN succeeds) [environment];
- m0 has 178,495 bytes (the program's storage) and its 4 bytes at 175623 are 0 (the POINTER PSAPTR, which has no VALUE, starts
  null) [initial storage];
- trs (TRNX) is nonempty, every record has 350 bytes and a valid amount (AmtOk: the 11-digit signed amount with 2 decimals
  decodes) [input domain], and trs is sorted by card number (CardsSorted: no adjacent-or-later pair out of order under the
  program's byte comparison) [input domain; stm_run_sorted only];
- trs has at most 50 card groups and each group at most 10 records [follows the program's tables: WS-CARD-TBL OCCURS 51,
  WS-TRAN-TBL OCCURS 10];
- every XREF record x satisfies XOk: 50 bytes, numeric 9-digit customer id and 11-digit account id, customer key found in CUST
  with a 500-byte record, account key found in ACCT with a 300-byte record, and the account id, the signed balance (12 digits,
  2 decimals) and a 3-digit customer field numeric [input domain];
- fuel F >= |trs| + |xrefs| + 100 [proof bound];
then Stm.run env F (Stm.initState m0 [(3,trs),(4,xrefs),(5,custs),(6,accts)]) stops with GOBACK, and in the final state: the
DISPLAY output is the per-XREF events in order followed by the 11 walk lines (out is kept newest first:
(xrefs.flatMap evsOfS).reverse ++ walkDisplays); STMT (file 1) = xrefs.flatMap stmtOfS and HTML (file 2) = xrefs.flatMap
htmlOfS; TRNX and XREF are read to the end; all six files are closed (mode := none, printed with
pp.structureInstances.defaults; logs/check_defs2.out). stmtOfS x is coblean's model of one statement: head, the transactions
whose card equals x's card in file order, totals and closing lines.
stm_run (Assembly.lean): the same hypotheses without CardsSorted, with the conclusion stated through the program's own table
scan (MainPost over grp trs).
stm_run_abort_cust / stm_run_abort_acct (Abend.lean): the same environment, storage and TRNX hypotheses; xrefs = pre ++ x :: post
with every record of pre satisfying XOk and x of 50 bytes with a numeric customer id; (cust) the customer key of x is not in CUST,
or (acct) it is found with a 500-byte record, x's account id is numeric and its key is not in ACCT; fuel as above. Then the run
ends in Fault.abend (-1) with: out = the three DISPLAY lines "ABENDING PROGRAM", "RETURN CODE: 23" and "ERROR READING CUSTFILE"
(or "... ACCTFILE"), then pre's events, then the 11 walk lines; STMT and HTML still open for output, holding pre's records.

## Kernel replay
- leancheck1lp.sh, one process per module (replay_cmds.txt, pjobs_v3 N=2): 43 Cobol modules (the copy's 2306Z-identical
  oleans; replay_modules_cobol.txt) + the 28 new modules (my out/lib) = 71/71 rc 0 (replay/*.tsv; longest 26.5 s). Negative
  control (evidence/controls/lc_neg): BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0 (control/). Lean core and the
  Lean meta library (imported by Examples.Stm.StmAttr) are toolchain modules and are not replayed.

## GnuCOBOL differential (V.stm)
- scripts/run_stm_check.sh runs coblean's tools/evidence/stm_check.sh in my copy with the pinned CardDemo sources and EBCDIC data
  (extracted from 59cc6c2f; equal to ~/coblean_corpus): "end: stop:Cobol.StopKind.goback file 1 (stmt.out): 1212 records,
  GnuCOBOL 1212, 0 differ file 2 (html.out): 6082 records, GnuCOBOL 6082, 0 differ displays after the walk: 0, GnuCOBOL 0, same
  AGREE" (logs/stm_check.out) = coblean's V.stm value.
- GnuCOBOL compiles CBSTM03A without lines 266-291 (the control-block walk: SET ADDRESS OF PSA/TCB/TIOT and its DISPLAYs), and
  stm_compare.py skips the first 11 DISPLAY lines of our run (walk = 11, line 15/31). Our run's 11 skipped lines and the
  theorem's walkDisplays (11 lines, #eval) are the same lines in the same order: "Running JCL : CREASTMT Step STEP040",
  "DD Names from TIOT: ", then STEPLIB valid, SYSPRINT null, SYSOUT null, TRNXFILE, XREFFILE, ACCTFILE, CUSTFILE, STMTFILE and
  HTMLFILE valid UCB (logs/compare_walk.out; the three lines my comparison flags differ only in EBCDIC padding bytes 0x40,
  shown as '@' in the ASCII-profile run). So the walk's output, which the differential never compared, is now fixed by the
  theorem for the address space Stm.asp.

## Notes
- coblean's message summarises XOk as "every XREF key found"; XOk also requires the record lengths (50, 500, 300) and numeric
  ids, balance and a 3-digit customer field. The theorem text above lists them.
- Producer compute: coblean's 308 guard logs ~/coblean_runs/guard/stmcore2_*.log sum to 7.660 core-h (305 runs by their exit
  totals, 3 cap kills by their CAP values; logs/coblean_guard_sums.txt) = the reported 7.66.

## Compute and disclosures
- This check: compile 0.094, replay 0.050, differential 0.001, eight short g1 runs 0.0014 core-h (about 0.15 core-h). The eight
  g1 logs are in the shared evidence/logs/g1 (20261027T1254-1310Z; listed in logs/g1_logs_mine.txt), not moved.
- Writes only in my two directories; in my copy I moved the prebuilt Stm/StmCore oleans aside (replay/.../aside/). Reads outside:
  ~/coblean_snapshots (snapshot, 2306Z), ~/coblean_runs/stmcore2/final_sha256.txt and guard logs, ~/coblean_corpus (cmp only),
  git reads of the CardDemo clone.
