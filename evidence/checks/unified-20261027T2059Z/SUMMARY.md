# Check by an agent: equiv-lean unified master 04d2599 (and b46c478)

An agent of the evidence-owner session, stamp 20261027T2059Z. Read-only on the inputs. Replay copy
~/fv_paper/replay/unified-20261027T2059Z (cp -rL, 0 links); outputs only here. Lean jobs at most 2 (pjobs_v3, floor 0),
each under coreh_guard_v2, ulimit -v 32 GiB, LEAN_NUM_THREADS=1. Inputs: freeze worktree /home/user/equivlean_freeze_04d2599-unified (sealed),
kit run dir /home/user/equivlean_work/scratch/eq-aeneas-auto/freeze_kit/runs/04d2599-unified-20261027T155940Z (RESULT.md 9f296d97, SHA256SUMS 1130b8ae).

## 1. Sums, tracked files, dependency versions: PASS
- Kit run SHA256SUMS: 597 entries, sha256sum -c OK.
- Freeze HEAD 04d2599628e4, 2564 tracked files, 0 uncommitted changes; not a partial clone (no promisor/partialclone config).
- Path dependencies (verified 20:57-20:58Z, progress log): vendor cirlean-e6ac99a = frozen e6ac99a sources (+VENDORED.txt);
  JimpleLean-20261026T2035Z = snapshot (SHA256SUMS OK); strictts-a15926a .lean 38/38 = git a15926a; coblean-20261024T2306Z =
  snapshot except docs/EVIDENCE_carddemo.md/.tsv; Aeneas fdebf20, clean.
- 1919 EquivLean .olean files in the build (the kit's module count). Copy integrity: 2063/2063 closure .olean files
  byte-identical to the freeze worktree and vendor dirs (olean_copy_vs_freeze.tsv).

## 2. Headline rows mapped to the paper (item2_map.tsv)
The kit's 144 rows: migration 16; restricted 1 (CBACT04C Java) + its Java total 1;
Java totals 8 (+ 8 run_term, + 3 JL totals); CBSTM03B 4 (Rust, Java, Java terminates, Java total);
TRX 9; jsmn 6; Adler-32 25; musl at e6ac99a 11; T4 rows 24 (C++ 9, Java 7, Rust 8) + Java totals
7 + hypothesis/class rows 3; nibbles 10; esdiff 2 (+ 4 helper lemmas).
- Missing from the 144: the restricted CBACT04C Rust and CBTRN02C Rust theorems (EquivLean.Modernize.Cbact04c.Rust.rust in
  Cbact04c.RustRun, EquivLean.Modernize.Cbtrn02c.Rust.rust in Cbtrn02c.RustRun). Both are in 04d2599; added here as rows
  145-146 (rows146.tsv) and checked with the rest. The 21 composite theorems and the 3 mutant refutations are not in
  04d2599 (they come in 89806a8 and b46c478, item 6).
- Rows with no paper result: 2 (Thrift.Java.rlb_uuid, rlb_uuid_total).

## 3. Statements: PASS
- 15/15 re-run print files give output byte-identical to the earlier checks' prints (stmt/compare.tsv): repin
  (findings, jsmn_c, musl_new incl. its same rc=1 message, rerun_eqr5, rerun_eqt4, rerun_eqt4jt_all, rerun_eqt4jt_special,
  rerun_t4nib, trx, trx_c), r4 Stmt, adler32 Stmt, eqjt print_terms, esdiff Check (both earlier outputs). The repin prints
  were themselves compared with eqr5, eqt4, eqt4jt, t4nib and eqT there.
- Generated statement files (*Statement*.lean, migration incl. restricted, and CBSTM03B): 22/22 byte-identical to the
  composite copy, 20 to the repin copy (CBSTM03B not present there) (stmt_src_identity.tsv).

## 4. Axioms, fresh processes: PASS
- 146/146 rows use only propext, Classical.choice, Quot.sound (EquivLean.Demo.Thrift.Java.thrift_classes_length: none); 84 fresh lean processes, one per row
  module, rc 0 (axioms/axioms_rows.tsv, axioms/permod/).
- One environment cannot import all rows: Cbact04c.JavaRunLib and Cbact04c.Every.JavaRunLib both define
  EquivLean.Modernize.Cbact04c.Java.drop_set_self.match_1 (axioms/Ax146.out). The rows build together at 04d2599 and are
  checked per module.

## 5. Kernel replay of the whole closure: PASS
- Closure of the 146 rows: 2063 modules (AeneasMeta replayed 17; EquivLean replayed 1041; Jimple reused 28; CIR reused 43; Cobol reused 43; StrictTS replayed 24; Aeneas reused 249; EquivLean reused 618; ). Mathlib-side packages and Lean core are not followed (as in earlier checks).
- Replayed here: 1082/1082 rc 0, including the 17 AeneasMeta modules added by hand (AeneasMeta .olean files 18/18
  byte-identical to the composite and repin copies). Reused: 981 (delta_reuse: 961 from repin, 20 more from composite;
  composite's overlay = its build for every closure module present, composite_overlay_vs_build.tsv).
- Controls: BadCtl rc=1 (kernel rejects the false theorem compiled without kernel check), GoodCtl rc=0. Guarded replay
  total 1.289 core-h.

## 6. b46c478: PASS
- b46c478 parent 89806a8, whose parent is 04d2599. Name status 04d2599..b46c478: A 19 (additions only).
- Composite.lean 24cd6e12, CompositeRestricted.lean de06bcf9 (both = the files the composite check
  passed), MutantRefutations.lean aadaeb06; the other 16 files are the mutants' .jimple inputs.

## Sentence for the appendix
All headline theorems check together at equiv-lean 04d2599 (cirlean e6ac99a, JimpleLean 20261026T2035Z, StrictTS a15926a,
coblean 20261024T2306Z, Aeneas fdebf20): the 144 headline theorems and the two restricted Rust theorems use only the
standard axioms, and all 2063 modules of their closure, including the 17 modules of Aeneas's metaprogramming library, pass
a kernel replay, 1082 replayed on our copy and 981 reused from byte-identical modules and closures of earlier replays.
