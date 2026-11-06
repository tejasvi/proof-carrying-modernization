RESULT: the 12 shared_ptr verdicts hold at cirlean e6ac99a as theorems about the semantics: statements byte-identical to T3, compile rc 0 from copies, 24/24 theorems print exactly propext, Classical.choice, Quot.sound, and 95/95 closure modules replay rc 0 (control rejected). The condition that made them conditional is still present: e6ac99a gives the 64-bit load of the two 32-bit counters the same one-element meaning as ffab71e (it reads the use count only); the load is not undefined there.

# T3 shared_ptr verdicts at cirlean next e6ac99a (veriforch re-check, labelled, outside PREREG_T): evidence check

Checked by an agent of the evidence owner (the evidence-owner session), 2026-10-27 02:44Z-03:04Z (date -u). Check dir:
~/fv_paper/evidence/checks/t3sp-20261027T0244Z. Replay dir: ~/fv_paper/replay/t3sp-20261027T0244Z.

## 1. Package and copies
- ~/veriforch/runs/postfreeze/t3_shared_ptr_e6ac99a: SHA256SUMS 820ff6724b34e4d3... (3,146 files), summary.json
  f13746f3c7fdaa06..., leanchecker_replay.log e71c2d624b668637... = announced; sha256sum -c 3146/3146 OK before
  (pkg_sumcheck_before.txt), in my copy (pkg_sumcheck_copy.txt) and after (pkg_sumcheck_after.txt).
- Copies (scripts/copy.sh, cp -rL, 0 symlinks, diff -rq empty): replay/.../pkg (1.3 GB) and replay/.../equivlean (the
  pin's sources and .lake/build, 701 MB; .lake/packages not copied: the closure has no Mathlib or other package).
- equiv-lean pin ~/equivlean_freeze_5ec2642-cirfrz: HEAD 5ec2642f0669..., worktree clean, not a partial clone. Its
  build is partial: no root EquivLean.olean and no EquivLean.Core.Facts.olean, which the verdict modules import.
  The package carries its own lib/EquivLean: 593 oleans byte-identical to the pin's, 13 pin demo modules absent, and
  Facts.olean 655f4570..., which equals my compile of the pin's Facts.lean (cmp-identical to the package's copy).
- cirlean pin ~/cirlean_frozen/next_e6ac99a_20261027: HEAD e6ac99a, clean; delivered MANIFEST_build.sha256
  (825e6dc0...) 126/126 OK before and after. The pin's lake manifest builds equiv-lean against a git-archive copy
  (~/equivlean_work/vendor/cirlean-e6ac99a): same CIR sources, but 3 of its 43 CIR oleans differ in bytes from the
  frozen build (CIR.Logic.CJTree, CIR.Logic.Loops, CIR.Tactic.Simprocs); the producer and I load the frozen ones; the
  kernel replay below covers the mix.
- The equiv-lean pin directory is not frozen: a lake build wrote 328 files into its .lake/build between 02:45:27Z and
  02:53:19Z, while I copied it (Facts.olean 3a985368..., the bytes of the live equiv-lean build's Facts, plus LoopAsync,
  Bridge.Cir.Corr and about 30 demo modules). diff -rq of the pin's build against my copy afterwards shows only files
  added in the pin, and Facts (absent when I copied; mine is 655f4570): no file the verdicts use changed
  (copy_vs_pin_build_after.txt).
- The producer's LEAN_PATH also lists the live ~/equivlean build as a last entry. Lean resolves a module by the first
  entry holding its root directory, so with lib/EquivLean present that entry is never consulted; my compiles omit it.

## 2. Sources and statements (compare/, scripts/compare_sources.sh)
- The producer's run_12_t3.py copies each verdict module (VOEquiv/<unit>_<old>_<new>.lean) and its two Gen modules from
  the T3 run directories and renames the namespace to VOEquiv.O<order>_...; it calls no model.
- Against the T3 certificates (my T3 check's replay copy): 12/12 verdict modules are byte-identical after undoing the
  rename; 24/24 Gen modules and the 3 VerifOrch support modules (Patch, Int, Cir.Patch) are byte-identical. So both
  statements of every verdict, their hypotheses and the definitions of VerifOrch.Cir.Bad and WT are textually the
  T3 ones: no hypothesis added, removed or changed.
- Statements: `equivalent`: for all pointers x0, x1 whose blocks exist in m (b < m.next) and every memory m,
  Equiv (ObsEq m) (evalCall new [x0, x1] m) (evalCall old [x0, x1] m), where Equiv is simulation both ways (the same
  inputs are safe, and safe runs have the same Exit and the same contents of every block that existed before the
  call). `changed_only_where_old_unsafe`: the same relation on every call outside Bad (ill-typed, or the old version
  not SafeRet).
- Front end: cir2lean of the frozen e6ac99a build, run on the T3 unit.cir inputs, regenerates all 24 Gen modules
  byte for byte except line 2, the header comment naming the input path (regen_e6ac99a_nocomment.tsv). The program
  representation is therefore the one e6ac99a produces; what changed under the verdicts is the CIR library (16 CIR
  source files differ between ffab71e and e6ac99a, cirlean_ffab71e_vs_e6ac99a_CIR.txt).
- equiv-lean b171660 (T3) -> 5ec2642: 262 commits, 1,511 files under EquivLean, mostly demos and the Modernize tree;
  in Core, Bridge/Cir and Tactic only Tactic/Ledger.lean. The 13 EquivLean modules in the verdicts' closure (Core.Sim,
  Core.Behaves, Core.Loop, Core.Facts, Bridge.Cir.{Obs, Loops, PtrLemmas, Behaves, ValSwap, Tactic, AutoCouple,
  PtrArgs}, Tactic.LoopAttr) are source-identical (equivlean_diff/summary.tsv). Nothing in equiv-lean touches these
  statements or proofs.

## 3. Build, axioms, kernel replay
- Compiled from the copy into replay/.../bld/lib (scripts/lc1.sh: lean -R, -j 1, Elab.async false, autoImplicit false
  as the T3 certificate lakefile sets; LEAN_PATH = bld/lib : frozen cirlean : my copy of the pin's build, where I
  compiled EquivLean.Core.Facts from the pin's source, scripts/lcE.sh): VerifOrch x3, 24 Gen and 12 verdict modules,
  all rc 0, no error and no sorry (compile/). My VerifOrch and Gen oleans are byte-identical to the producer's; my
  12 verdict oleans differ in bytes (the autoImplicit option), and both sets are replayed below.
- Axioms, fresh process per module (scripts/axcheck.sh, axioms/axcheck.tsv): for all 12, `equivalent` and
  `changed_only_where_old_unsafe` each print exactly [propext, Classical.choice, Quot.sound]; no sorryAx, no error.
  The compile outputs print the same 24 lists.
- Kernel replay (leancheck1lp.sh per module, LEAN_NUM_THREADS=1, guarded, pjobs N=2): 95/95 modules rc 0 (replay_tally.txt, replay/): the 12 verdict modules, 24 Gen, 3 VerifOrch, the 13 EquivLean modules (with my Facts) and the 43 CIR modules of the pin's closure of CIR. The producer's 12 verdict oleans also replay rc 0 with its own lib first (replay_producer/).
- Negative control (evidence/controls/lc_neg sources, compiled into replay/.../ctl): BadCtl compiles, prints "does not
  depend on any axioms", and leanchecker rejects it (rc 1, declaration type mismatch); GoodCtl rc 0 (control/).

## 4. The condition: the 64-bit load of the two 32-bit counters
- Why conditional in T3: libstdc++'s _Sp_counted_base<_S_atomic>::_M_release (shared_ptr_base.h:336) loads
  _M_use_count and _M_weak_count, two adjacent 32-bit record members, as one 64-bit word and compares it with
  1 + 2^32 (the fast path when both counts are one). The cirpun scan flags this load (FLAG, dyn rec, load s64 of an
  s32 object) in all 12 closures, old and new. T3 counted the verdicts as holding only under the semantics' reading
  of that load.
- In the Gen code the verdicts evaluate, all 24 modules define fn_std_Sp_counted_base_M_release; it takes member 1
  (int32) of the _Sp_counted_base record with getMember, bitcasts the pointer to int64*, and compares the atomic load
  with the constant 4294967297 (__unique_ref) (e.g. Gen.v9197ce06.../Unit.lean 3661-3710).
- e6ac99a's code: punning2 (2d65713) makes a scalar access undefined (Mem.punnedAccess, CIR/Semantics/Basic.lean
  203-213, checked first by loadTy at 215 and storeTy at 231) only when Ty.atPath gives the element type, and Ty.atPath (183-186)
  follows array elements only and returns none at a record member, so punnedAccess is false for this load. loadTy
  then reads the member's stored value and accepts it as a 64-bit integer (fitsTy: any 32-bit value is in the 64-bit
  range). unionpun (6653cbe, ad01e8e) concerns union members of the same size; these are struct members.
- Probe (probe/probe2.cpp, a class with a vptr and two int members, heap and stack, plain and __atomic_load_n;
  probe2_results.tsv): natively the load returns use + 2^32 * weak (1,1 -> 4294967297); cirrun at e6ac99a and at
  ffab71e both return the use count alone (1,1 -> 1; 3,2 -> 3), and the fast-path test "both counts are one" is true
  natively and false on both pins. (probe.cpp's heap cases used `new Base()`, whose zeroing memset both pins reject
  as UB "memset: no zero value for the type"; probe2 uses `new Base`.)
- Scan at e6ac99a: cirpun (the T3 tool copy, f365f63; SHA256SUMS 10/10 OK) re-run on the 24 closures: 24/24 outputs
  byte-identical to T3's; 22 FLAG and 2 FLAG+CHAR (~TFileTransport); every closure keeps the 2 FLAG rows for the
  counter load. The scan reads unit.cir, which is unchanged, and its README already states that at 2d65713 a punned
  access into a record member is not checked.
- Status: the condition is still present, unchanged. At e6ac99a the load is neither undefined nor given its machine
  meaning: it keeps the one-element meaning it had at ffab71e (it reads the use count only). The 12 verdicts hold at
  e6ac99a as statements about the semantics, with the same dependence on this reading as in T3. The paper's T3
  sentence that the later C semantics "treats them as undefined" does not hold for this access.

## 5. Producer's records and spend
- summary.json and the 12 records: verdict equivalent, holds, both theorems without errors, axioms the standard three.
  `old_verdict_87a2905` is a constant "equivalent" written by the script, not a read value. `replay_olean_ok` means
  only that the compile returned 0; the producer's leanchecker_replay.log replays the 12 verdict modules alone (12
  lines, rc 0), not their closures.
- Spend: no model calls (the proofs are the T3 certificates' proofs). Producer guard log (guard.log): 100 guarded
  compiles, 0.173 core-h in all; 52 exited 0 and 48 exited 1 between 02:12:35Z and 02:41:31Z, before the final pass;
  the logs of the failed attempts are not in the package (logs/ holds the 12 final verdict compiles).

## 6. Discrepancies and notes
- The message says the condition-bearing verdicts were "replayed" at e6ac99a and all hold. They hold as statements
  about the semantics, but the re-check does not change their conditional status (section 4).
- "all 12 VOEquiv.O* .oleans replay under leanchecker": true, but that log covers the 12 modules alone; the closure
  replay here is mine.
- When the producer ran and when I copied the pin, its build had no EquivLean.Core.Facts.olean; the package supplies
  a compile of the pin's source, identical to mine. The producer's LEAN_PATH lists the live ~/equivlean build last;
  it is shadowed and was not needed.
- The equiv-lean freeze directory changed during this check (section 1): a later reader of that directory will find a
  build that differs from the one the producer and I used (Facts.olean 3a985368 there, 655f4570 in both runs).
- 48 of the producer's 100 guarded compiles exited 1 before the final pass; their logs are not kept.
- The probe's ffab71e cirrun is my T3 replay copy's (01e5df80...), the same file as
  ~/veriforch_frozen/T3_final_20261025T173358Z/deps/cirlean-ffab71e/.lake/build/bin/cirrun.

## 7. Compute and disclosures
- 0.194 core-h in all (guard/, one coreh_guard_v2 log per job; finalize.sh sums them): compiles, 107 replays, probe, scans.
- Reads outside my two directories: the producer package, the two pins, ~/equivlean_work/vendor/cirlean-e6ac99a
  (olean hashes only), my T3 check and replay directories, ~/cirlean_work/deliver/next_e6ac99a (manifest), the
  ClangIR toolchain (~/cirlean_work/toolchain/upstream-4955d32b) for the probe, and evidence/tools and
  evidence/controls/lc_neg (read only). git read-only with GIT_ALLOW_PROTOCOL=file. No writes outside my two
  directories; no messages sent. Guard logs are in guard/ (not evidence/logs/g1). In my build dir I removed two empty
  directories I had created (bld/lib/EquivLean/Core, bld/lib/EquivLean) with rmdir, so that Lean would find EquivLean in
  the pin's build.

## Files
SHA256SUMS covers this directory: compile/, axioms/, replay/, replay_producer/, control/, compare/, scans/, guard/,
scripts/, the probe results, the tallies, the pin and package checks, and the producer-vs-pin olean lists.
