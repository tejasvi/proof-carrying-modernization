RESULT: equiv-lean composite theorems (ba05f6e on r4-cbstm03b, 89806a8 on unified) CONFIRMED: 21/21 statements equal
the generated Statements' binders with the composite conclusions; 21/21 standard axioms; closure replay complete.

# Check of the composite migration theorems (an agent of the evidence-owner session; written 2026-10-27T20:03:38Z)
Copies: ~/fv_paper/replay/composite-20261027T190730Z: equivlean/ = cp -al of the frozen kit ~/equivlean_freeze_0fd209e-r4t
(read-only; kit manifest 4391/4391 OK before 19:09:58Z and after; 0fd209e..5d852da = README only), equivlean_work/ =
cp -rL of the four vendor pins and the Aeneas backend (0 links), overlay/ = hard links of the kit library with writable
directories for the two new oleans, newmods/src = the two sources from git (ba05f6e).

1. Commits (commit_diffs.txt): each adds exactly EquivLean/Modernize/Composite.lean (883 lines) and
   CompositeRestricted.lean (76 lines), no other file (no lakefile or root import change). The two files are
   byte-identical on both branches: 24cd6e12..., de06bcf9... (composite_file_shas.txt).
2. Compiled in my copy (lean -R, -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false): Composite.olean
   aa69a453..., CompositeRestricted.olean 1871455c..., both byte-identical to the producer's oleans in ~/equivlean_wt_r4b.
3. Statements (stmt/CmpComposite2.out, stmt/CmpRestricted.out; a Lean meta check): for all 21 composites, the binder
   chain has the same length as the generated Statement's and each binder type is defeq in order; the last conjunct
   of the conclusion is defeq to the Statement's conclusion. Conjuncts: Rust [Safe c, Exists (run = .ok out),
   Equiv Rel run c] (11 theorems incl. the restricted CBACT04C and CBTRN02C Rust and CBSTM03B), Java [Safe c, MTerm,
   (exists MExec) and (forall MExec -> post), Sim Rel (Call.mk ...) c] (10 incl. the restricted CBACT04C Java and
   CBSTM03B). Printed examples in stmt/Print.out, stmt/PrintRestricted.out.
4. Axioms (fresh process, stmt/Axioms.out, AxiomsRestricted.out): 21/21 exactly [propext, Classical.choice, Quot.sound].
5. Closure (closure/): environment list of both modules = source closure + the 2 modules = 1204 followed modules (866
   EquivLean + 2 new, 249 Aeneas, 17 AeneasMeta, 43 Cobol, 27 Jimple); Mathlib, batteries, aesop, Qq, plausible,
   importGraph, proofwidgets, LeanSearchClient at the same revisions as the repin copy (lake-manifest). Reuse against the
   repin check's copy (replay_pass_mods + its validly reused modules, 1751): 336 reused (olean and closure byte-identical),
   849 replayed; the 17 AeneasMeta modules, which no earlier closure followed, replayed too; the 2 composites replayed.
   868/868 rc 0 (max 34.4 s), BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0.
6. What the composites use: Rust: Safe c from the headline Equiv via Equiv.safe_iff with the Rust normal return from
   the program's run_spec (call_spec for CBSTM03B). Java: Safe c from the COBOL-side program theorems (Glue.cobol_outputs,
   CardDemo.<P>.<P>_lists, cbtrn01c_verifies_all, the every/any theorems' signal, cbstm03b's call), MTerm from run_term
   (java_terminates for CBSTM03B), totality from run_total (java_total), Sim from the headline java theorem.
7. Cost: 0.998 core-h in 875 guarded jobs; pjobs 19:17:51Z-20:02:17Z.
Note: the 17 AeneasMeta modules were outside the closures of earlier checks (closure_multi/delta_reuse do not follow that
prefix); all 17 replay rc 0 here.
