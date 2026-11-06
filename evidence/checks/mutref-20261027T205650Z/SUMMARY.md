RESULT: equiv-lean's Lean refutations of the three A3 Java timeout mutants (MutantRefutations.lean aadaeb06..., commits
47d9ce3 on r4-cbstm03b and b46c478 on unified) CONFIRMED: 3/3 theorems are ¬Statement_<mut> with Statement_<mut> = the
generated Statement with only the program substituted; standard axioms; kernel replay rc 0 with both controls behaving.

# Check of the mutant refutations (an agent of the evidence-owner session; written 2026-10-27T21:12:42Z)
Copies: ~/fv_paper/replay/mutref-20261027T205650Z: src/ = the 17 committed files; overlay/ = cp -al of the composite
check's overlay (kit library + composites; 10727 files, 0 symlinks); only MutantRefutations.olean/.ilean written there.
Producer worktrees read-only (no promisor config; GIT_ALLOW_PROTOCOL=file).

1. Commits: 47d9ce3 (parent ba05f6e) and b46c478 (parent 89806a8; both parents are the composite-checked commits) each
   add exactly EquivLean/Modernize/MutantRefutations.lean and 16 Jimple files in EquivLean/Demo/Gen/Jimple/
   mut_cbcus01c_j4 (3), mut_cbact01c_m2 (5), mut_cbact04c_m5r (8); same list and blobs on both (files_*.txt). PASS.
2. Provenance: J4 and M5r Jimple differ from the originals exactly as the A3 records (j4_*.diff, m5r_*.diff: J4 two
   swapped field reads in fmtRecord; M5r one constant "DEFAULT   " -> "DEFUALT   " in run). M2 regenerated from the
   A3-stored mutant source mut/M2/Cbact01c.java (d3cd9383) with javac --release 17 + Soot 4.7.1 (A3 recipe,
   scripts/jregen_m2.sh, m2soot.log): 5/5 files byte-identical to the committed ones (the cobdatft call dropped in run). PASS.
3. Statements (stmt/Cmp.out, Cmp2.out, Print2.out; Lean meta checks in a fresh process): for each mutant the constants
   of Statement_<mut> and the generated Java Statement differ only in {Gen.prog, runRef} vs {Gen<mut>.prog,
   runRef_<mut>}; after that substitution the bodies are alpha-equal (J4, M2 also exactly equal; M5r differs only in the
   hygienic name of the clock lambda "fun _ => clk"); 0 top-level binder differences. runRef_<mut> is the same
   expression as runRef with Gen -> Gen<mut> (the .ref of the mutant program's run method); MethodRef.sig equal for
   all 3; J4's runRef is even defeq to the original (its mutation is outside run; MethodRef carries the method body,
   so M2's and M5r's refs differ only by their mutated run bodies). Theorems: mut_J4_not_statement : ¬Statement_J4,
   mut_M2_not_statement : ¬Statement_M2, mut_M5r_not_statement : ¬Statement_M5r. PASS.
4. Evaluator: runMK P fuel m args σ := runCall P fuel 10 m args σ (structural recursion on depth and statement fuel;
   no partial/unsafe/opaque/extern/implemented_by in the file); runs_of_runMK : runMK P fuel m args σ = some
   o.toOutcome -> EquivLean.Runs {P, m, args, σ} o (proved via runCall_sound/runBody_sound); EquivLean.Sim R t s :=
   Safe s -> Safe t ∧ ∀ ot, Runs t ot -> ∃ os, Runs s os ∧ R ot os, so the lift reaches the Runs of the Statement.
   Axioms of runs_of_runMK, of_checkRunMK, check_{J4,M2,M5r}_eq: [propext, Classical.choice, Quot.sound]. The
   evaluations are decide +kernel (no native_decide; source grep: no native_decide/ofReduceBool). PASS.
5. Axioms (fresh process, stmt/Axioms.out): the 3 refutations exactly [propext, Classical.choice, Quot.sound]. Own
   body walk (stmt/Walk.out; does not use the oleans' precomputed axiom tables): same 3 axioms for each theorem and for
   all 420 constants of the module (11456 constants reached, 0 missing); Lean.ofReduceBool, ofReduceNat, reduceBool,
   reduceNat, trustCompiler, sorryAx not reached. PASS.
6. Compile and replay: my compile of the committed source (lean -R, -DautoImplicit=false -DrelaxedAutoImplicit=false
   -DElab.async=false; 56 s) gives MutantRefutations.olean ddb05c25..., byte-identical to both producers' oleans.
   leanchecker MutantRefutations rc 0 (56.4 s, replay/); BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0
   (replay_controls/). Closure (closure/mods_env.txt): 104 followed modules (34 EquivLean, 43 Cobol, 27 Jimple) plus
   toolchain Init/Std/Lean; all 104 byte-identical to the composite check's (closure/reuse.tsv): 31 replayed there rc 0,
   73 reused there; the only module outside the composite closure is MutantRefutations. PASS.

Witnesses (one record per input file; every premise of the Statement proved; n = 2, 2, 5):
- J4 (CBCUS01C): a customer record of zeros and spaces with first name "A" and last name "B"; the mutant's second
  display line has "B" at position 9, the COBOL program displays the record ("A" there).
- M2 (CBACT01C): an account record of zeros and spaces with reissue date "2024-01-31"; the mutant's first output
  record carries a reissue date different from the COBOL program's (the model's) converted date.
- M5r (CBACT04C Every): account 1 in group GRP1, a card cross-reference, a category balance of 100 and one rate
  record for group DEFAULT; GRP1 has no rate record, so the COBOL program uses DEFAULT and does not abend (model
  abended = false), while the mutant looks up "DEFUALT" and returns abended = 1.

Cost: 0.034 core-h in 6 guarded jobs (guard_*.log), plus the M2 regeneration (javac + Soot).
