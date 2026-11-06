RESULT: the T4 Java nibbles 14/15 package (equiv-lean a9c8e23) agrees with the delivery: tracked files 2420/2420 = a9c8e23, manifest 4238/4238 (before and after); the 10 new modules compile from source in our copy with no error or sorry; the 10 new totals and all 108 headline rows print exactly propext, Classical.choice, Quot.sound (thrift_classes_length: no axioms); the import closure of the 10 new modules (111 modules) passes the kernel replay: 72 replayed rc 0 + 39 reused (byte-identical to the 613c77c check's passing copy); controls as expected. No change to previously checked statements.

# T4 Java nibbles 14/15 (equiv-lean t4-java-nibbles a9c8e23; labelled package by JimpleLean's session T4Nib-20261027T0053Z): evidence check

Checked by a fork of the evidence owner (the evidence-owner session), 2026-10-27 05:20Z-05:46Z (date -u). Check dir: this directory. Copies:
~/fv_paper/replay/t4nib-20261027T0520Z/{equivlean, equivlean_work} = rsync -rtL (symlinks followed; 0 links in the copy) of the
kit tree ~/equivlean_freeze_a9c8e23-t4nib (without its .git pointer and .tmp) and of its path dependencies
(~/equivlean_work/vendor/{cirlean-28e2380, JimpleLean-20261025T2312Z, coblean-20261024T2306Z, strictts-a15926a},
~/equivlean_work/dl/aeneas/backends/lean), mirroring the ../equivlean_work layout of the lake manifest.

## 1. Objects and hashes
- Manifest ~/equivlean_work/scratch/main/t4/SHA256SUMS_a9c8e23-t4nib.txt: sha256 56c59628a985672e1870215d0a80f596f8d8353284625662ef283d8f9c2bd326
  (= the message), 4238 lines (tracked files + built EquivLean oleans); sha256sum -c in the tree 4238/4238 OK before
  (manifest_check_before.txt) and after (manifest_check_after.txt), and in our copy 4238/4238 (manifest_check_copy.txt).
  The tree is read-only (no file with a write bit).
- git (GIT_ALLOW_PROTOCOL=file, GIT_OPTIONAL_LOCKS=0, read-only; equivlean is not a partial clone): HEAD a9c8e2366058683c2b2d2848ba2c3ee5430c23f3;
  git hash-object of all 2420 tracked files = their blob ids at HEAD (tracked_vs_head.txt: 0 DIFF).
- d35b1e4 -> a9c8e23 (diff_d35b1e4_a9c8e23.txt): exactly 10 added files, EquivLean/Demo/Thrift/Java/Term/{GttAll, RfbAll,
  RfbAllP, RfbAllT, RlbAll, RlbAllP, RlbAllT, RsbAll, RsbAllP, RsbAllT}.lean, plus README.md and HANDOFF_20261023.md modified
  (one handoff commit 0f69ac7 between). 613c77c (the R7 check) -> a9c8e23 (diff_613c77c_a9c8e23.txt): 77 added files (these 10;
  the merged R5 jsmn, musl, ledger, XLang files) and only README.md and HANDOFF modified: no previously checked Lean file
  changed, so no previously checked statement changed.
- Vendor copies = the R7 check's copies (replay/eqt4jt-20261026T2003Z; diff -rq differs only by the .git pointers we leave out);
  aeneas identical.

## 2. Statements (stmt/check10.lean, printed in a fresh process: stmt/check10.out, 0 errors; = the sources)
Common hypotheses of the field/list/set theorems: Contains P [the Thrift classes], Valid P (tContracts R).env,
NoRedeclR/NoRedeclL/NoRedeclS P, TransportTerm P R, TRepConc P R (the premises of the other field and list/set totals of R7).
- gttAll_total (hyp Contains P [cpC, tpeC, teC]): getTType(byte) on every byte, with only the argument shape and an
  initialized TProtocolException class as precondition: every call terminates, and every outcome either returns the TType of
  the nibble (b mod 16) with the state unchanged (gttN) or, only when the nibble has no TType (14 or 15), throws an object of
  class TProtocolException (gttE).
- rfbAll_total / rlbAll_total / rsbAll_total: readFieldBegin() / readListBegin() / readSetBegin() on every header byte,
  total correctness: the contracts of rfb_body/rlb_body/rsb_body without the known-nibble precondition (NibbleOK/NibbleOKL);
  on a header byte whose type nibble has no TType the exception is getTType's TProtocolException (rfbBad etc.), otherwise
  the outcomes are as the earlier contracts state.
- rfb_nib1415_total: a field header byte u != 0 with type nibble >= 14 (14 or 15): readFieldBegin() terminates and every run
  throws a TProtocolException. rlb_/rsb_nib1415_total: a list/set header byte with element nibble >= 14 and a valid size
  (listSizeJ, 0 <= size, InLimit): readListBegin()/readSetBegin() terminates and every run throws a TProtocolException.
- rfb_nib1415_spec_total: for a header built as Spec.fieldHeader last id ty with ty in {14, 15} (id a valid i16), the
  specification's Spec.readFieldHeader reads it as a field of type ty, AND Java's readFieldBegin() terminates and every run
  throws a TProtocolException. rlb_/rsb_nib1415_spec_total: for Spec.listHeader size ety with ety in {14, 15} (size < 2^31,
  within the limit), Spec.readListHeader reads it as (size, ety), AND Java's readListBegin()/readSetBegin() terminates and
  every run throws a TProtocolException. These three state the difference between our specification and Java on these
  headers as Lean results (the README says so).
- Native comparison (checks/t4nib-native-20261027, mine_run_jar.txt = coordinator_run_nib1415_jar.txt apart from the jar path):
  Java's TCompactProtocol (thrift-java f0eb8b84) throws TProtocolException "don't know what type: 14/15" on [1E]/[1F]
  (readFieldBegin) and [0E]/[0F] (readListBegin, readSetBegin), on both transport paths: consistent with the theorems.

## 3. Compile and axioms
- The 10 new modules compiled from source in our copy, in dependency order, one core each, guarded (scripts/compile_levels.sh,
  compile_one_v2.sh; lakefile options autoImplicit/relaxedAutoImplicit false, Elab.async false): 10/10 rc 0, no error, no
  sorry (compile/summary.txt); the modules' own #print axioms lines give exactly [propext, Classical.choice, Quot.sound] for
  all 10 totals. Our oleans replace the producer's in our copy (the producer's 10 kept in replay/.../producer_oleans); the
  bytes differ (new_oleans_mine_vs_producer.txt), as do the oleans of 7 unchanged modules between the R7 copy and this
  build (Zz, RfbD, Gam, Gtt, Wv32, RfiD, Vacc; identical sources): all are replayed below.
- 108 headline rows of the producer's audit (producer_audit.json -> producer_headline108.tsv: 17 CardDemo headline + 81
  postfreeze rows + the 10 new totals), printed in fresh processes (axioms/): Demo_Cir 10/10, Demo_XLang 15/15, Demo_Thrift
  45/46 exactly the three standard axioms + thrift_classes_length (decide, no axioms), Modernize 37/37 (one row per process:
  Cbact04c.JavaRunLib and Cbact04c.Every.JavaRunLib define the same auxiliary name and cannot be imported together; the
  producer's audit also uses one file per row). Total 107 standard + 1 without axioms = the producer's audit.
- The 8 known Popcount theorems of the producer's sweep (EquivLean.Demo.Aeneas.Popcount: popcount_swar_spec, popcount_spec,
  swar_step_toNat, popcount_equiv_swar, swar_step, and_sub_lt, swar_toNat_le, swar_le) use, besides the three, bv_decide's
  native-evaluation axioms <thm>._native.bv_decide.ax_N (axioms/popcount.out); the module's doc says so. No Aeneas module is
  in the closure of the 10 new theorems.

## 4. Kernel replay
- Import closure of the 10 new modules (tools/closure_multi.py over EquivLean, Jimple, Aeneas, Cobol, CIR, StrictTS):
  111 modules = 84 EquivLean + 27 Jimple (closure10.tsv); outside them only Lean core (Lean, Std) is imported.
- tools/delta_reuse.py against the R7 check's copy (replay/eqt4jt-20261026T2003Z; pass list = its 1898 passing modules):
  39 reused (olean and whole closure byte-identical to a module that passed there), 72 to replay (10 new; 7 unchanged
  modules whose oleans differ; 55 importers of these) (delta_eqt4jt.*).
- tools/leancheck1lp.sh with the copy's LEAN_PATH (leanpath.txt), guarded, two lanes (pjobs_v3): 72/72 rc 0 (replay/*.tsv;
  largest 4.8 s). Controls (replay/.../ctl, rebuilt here): BadCtl rc 1 "(kernel) declaration type mismatch", GoodCtl rc 0
  (replay_controls/; a first try failed before compiling because lean requires the input file under its working directory).

## 5. Cost
- Producer: the kit run a9c8e23-t4nib-20261027T011027Z rebuilt the whole workspace, 1819 modules; times.csv sums to
  38,512 s = 10.698 core-h (producer_times.csv; the message's 10.70); the 10 new modules took 578.5 s of it.
- This check: 0.293 core-h over its guarded jobs (guard/) + 0.008 for the copy (guard_g1/).

## 6. Discrepancies and disclosures
- None in the delivery. Notes: our olean bytes for the 10 new modules and 7 unchanged modules differ from those of the kit
  build / the R7 copy (sources identical); every such module was replayed rc 0, so the difference does not affect any result.
- Disclosures: compile attempt 1 used a separate output root, which hides the EquivLean package (lean looks a package up in
  the first matching search-path root); attempt 2 elaborated (gttAll_total standard axioms) but could not write the olean
  because the copy kept the read-only permissions; we then set u+w on our copy's Term build directory and the 10 olean/ilean
  files only (inodes differ from the producer's). We edited our own script compile_levels.sh with sed -i (backup .bak kept).
  Three g1.sh guard logs of this check (copy, closure, delta) were written to evidence/logs/g1 and moved to guard_g1/.
  Nothing was written outside our two directories otherwise; git was used read-only; no lake was run in any producer tree.
