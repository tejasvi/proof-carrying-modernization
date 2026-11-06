# Check by an agent: termination theorems behind the Java "total" theorems (fork of the evidence-owner session; written 2026-10-27T17:59:01Z)

Copy: ~/equivlean_freeze_613c77c-t4jt (HEAD 613c77ccf4eb...; = 9f0e5fb + T4 files, so its migration modules are 9f0e5fb's),
read-only, with its own oleans and the version-named vendor dirs of its lake-manifest (leanpath_613c77c.txt). Lean v4.35.0
run from this dir with LEAN_PATH set (no lake); guards guard_*.log, total 0.01 core-h.

1. Types (mterm_report2_613c77c.out): Jimple.MTerm is an inductive predicate over method bodies (BTerm), "every execution
   terminates, whatever the nondeterministic choices"; Jimple.total_of_sat_mterm : Sat P m S -> (forall args s, S.pre args s
   -> MTerm P m args s) -> forall args s, S.pre args s -> (exists o, MExec P m args s o) /\ forall o, MExec .. o -> S.post ..;
   Jimple.TermVC.mterm : Valid P Gamma -> (callee ContractTerm) -> TermVC .. -> forall args s0, S.pre args s0 -> MTerm P m args s0.
2. Migration (8 headline run_total): each run_term states forall args s, runSpec.pre args s -> MTerm Gen.prog runRef args s;
   each run_total's proof is total_of_sat_mterm applied to the program's run_sat and its own run_term (closure walk + method-
   ref match: 8/8; the printed term for Cbact02c is total_of_sat_mterm (sat_runSpec_of_J JL.run_sat) Cbact02c.Java.run_term).
3. T4 (68 *_total of STATEMENTS.tsv): every total has the form (exists o, MExec) /\ forall o, MExec -> C, and its proof is
   <MTerm.run (X_term ... args s hpre ...), X_sat ...> with an MTerm theorem for the same method applied to the total's own
   hypotheses and inputs (printed for rb_total, wcb_total, wi16_E_total; closure walk + method-ref head match for all 68).
   66 use one of the 22 *_term rows (each concludes MTerm P <m>Ref args s; t4_term22_statements.txt), wi16_E_total via
   bwi16_term; wcb_total and wcb_E_total use wcb_termI (not among the 22 rows; statement in wcb_termI_statement.txt:
   Contains, Valid, NoRedeclW, TransportTerm, TRepConc, wcbSpecI.pre -> MTerm P wcbRef args s). No total lacks one.
Files: mterm_report.lean/.out, mterm_match.lean, mterm_match2_613c77c.out, mterm_print.lean/_613c77c.out, rows_613c77c.tsv,
t4_total_to_term.tsv, match2_613c77c.txt, t4_term22_statements.txt, wcb_termI_statement.txt, PROGRESS.md.
