RESULT: the v2 pin checks out. It is pin 1251Z plus exactly Examples/StmCore/SortedAbort.lean (with its 8 build files),
SHA256SUMS and STMCOR_PROGRESS.md. The three corollaries compile from source against the closure that
checks/stm03ab-20261027T1252Z compiled and replayed, use exactly [propext, Classical.choice, Quot.sound], and replay in
the kernel (from-source module 1/1, and leanchecker --fresh of it rc 0; the pin's prebuilt Stm/StmCore modules plus
SortedAbort 29/29). Controls behave.
# StmCore v2 pin: sorted-abort corollaries (checks/stmcor2-20261028T084846Z; an agent; written 2026-10-28T08:56:36Z by date -u)
Pin: ~/coblean_snapshots/coblean-pin2306Z-cbstm03ab-v2-20261028T0658Z (producer: coblean helper, ~/coblean_runs/stmcor).

## Inputs
- diff -rq --no-dereference vs pin 1251Z without .lake: only SortedAbort.lean, SHA256SUMS, STMCOR_PROGRESS.md
  (inputs/diff_src_no_lake.txt); in full, only the 8 SortedAbort build files besides them (inputs/diff_full.txt). So every
  other file, the Cobol build subset (lib/lean/Cobol*, ir/Cobol*) and all 28 Stm/StmCore oleans included, is byte-identical to 1251Z.
- sha256sum -c of the pin's SHA256SUMS (8c25cb98...): 839/839 OK (inputs/pin_sha256_check.txt). SortedAbort.lean b34a552d...
- The pin's 43 Cobol oleans are byte-identical to those of the copy that stm03ab replayed (closure/pin_cobol_vs_oldcopy.txt);
  Cobol.olean be3132eb.

## Build from source, statements, axioms
- scripts/compile_sortedabort_v2.sh: SortedAbort.lean (copied to src/, same sha) compiled with Lean v4.35.0 and the lakefile's
  leanOptions, one thread, against a copy (job tmp) of the 28 Stm/StmCore oleans that stm03ab compiled from source and replayed
  (28/28 byte-identical, closure/copy_vs_replayed_oleans.txt) and that check's copy for Cobol: rc 0, no warnings
  (logs/compile_sortedabort_v2.out; v1 failed only because a separate build dir shadowed the Examples root). My olean
  (228417fa..., build/) differs in bytes from the pin's prebuilt one (a067450f...), as stm03ab's from-source oleans do.
- Fresh process (axcheck/AxCheck.lean, logs/axcheck.out): the three corollaries depend on exactly [propext, Classical.choice,
  Quot.sound]; planted controls flagged: plantedSorry -> [sorryAx], plantedAxUse -> [plantedAx].
- Statements in words (full types in logs/axcheck.out):
  abortPost_sorted: for every transaction list trs sorted by card (CardsSorted trs) and every pre, custs, accts, msg, st:
    AbortPost (grp trs) pre custs accts walkDisplays [] [] msg st holds iff st.out = msg ++ (pre.flatMap (evsOfS trs custs
    accts)).reverse ++ walkDisplays, file 1 (STMT) = {mode output, recs pre.flatMap stmtOfS}, file 2 (HTML) = {mode output,
    recs pre.flatMap htmlOfS}. (AbortPost states the same through the program's own grouping grp trs with evsOf/stmtOf/htmlOf;
    the bridge is evsOf_sorted, stmtOf_sorted, htmlOf_sorted, already in 1251Z.)
  stm_run_abort_cust_sorted: the hypotheses of stm_run_abort_cust (fixed address-space model asp, every OPEN succeeds, the
    178,495-byte storage with PSAPTR null, trs nonempty with 350-byte records and valid amounts, at most 50 groups of at most
    10, xrefs = pre ++ x :: post with every record of pre XOk, x of 50 bytes with a numeric customer id whose key is not in
    CUST, fuel >= |trs| + |xrefs| + 100) plus CardsSorted trs; then the run ends in Fault.abend (-1) (the model's marker for
    an abend without user code) with st.out = custMsg ++ (pre.flatMap evsOfS).reverse ++ walkDisplays (custMsg = EBCDIC
    "ABENDING PROGRAM", "RETURN CODE: 23", "ERROR READING CUSTFILE", newest first) and STMT/HTML still open for output,
    holding pre.flatMap stmtOfS / htmlOfS.
  stm_run_abort_acct_sorted: the same for a missing account: x's customer key found at i with a 500-byte record, x's account
    id numeric and its key not in ACCT; acctMsg ends "ERROR READING ACCTFILE".
- Limits for a paper sentence: the corollaries add no case beyond stm_run_abort_cust/acct; they restate those abends, under
  the added sortedness premise, through the functional models evsOfS/stmtOfS/htmlOfS that stm_run_sorted uses. pre is the
  list of cross-reference records before the one whose customer or account is missing.

## Kernel replay (tools/leancheck1lp.sh, one process per module, pjobs_v3 N = 2; logs/pjobs.log)
- A (from source): Examples.StmCore.SortedAbort rc 0 (0.8 s; replay_A/). Its closure is the 28 Stm/StmCore oleans and 43
  Cobol oleans that stm03ab replayed (71/71 rc 0), byte-identical (above), so those results carry over (the delta_reuse rule:
  same olean bytes for the module and its whole closure); toolchain modules are not replayed, as in stm03ab.
- B (the pin's prebuilt oleans, which no earlier check replayed): the 28 Stm/StmCore modules + SortedAbort, 29/29 rc 0
  (replay_B/; longest Examples.StmCore.Mainline2 21.4 s); the 43 Cobol oleans = the replayed copy's.
- Controls (evidence/controls/lc_neg): BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0 (control/).
- leanchecker --fresh on the from-source SortedAbort, which replays its whole import closure (toolchain modules
  included) from an empty environment: rc 0 in 187.0 s (fresh/fresh.tsv; scripts/fresh_sortedabort.sh; guard cap 0.4
  core-h, used 0.052, logs/20261028T085548Z_stmcor2fresh.log).

## Compute and disclosures
- 35 g1 runs (compile 2, axcheck 1, replay 32): 0.028 core-h by their guard logs (logs/g1_logs_window.txt; all exited 0);
  the fresh replay 0.052 core-h (own guard log). Total about 0.080 core-h.
- Writes: this directory and the job tmp copy /home/user/.claude/jobs/8a4f16ec/tmp/stmcor2_lib (95 MB, copies, no
  links). Reads: the pin, pin 1251Z, replay/stm03ab-20261027T1252Z (out/lib, snap lib; read only), evidence/controls/lc_neg.
  build/lib/Examples/StmCore is an empty dir left by the failed v1 compile.
