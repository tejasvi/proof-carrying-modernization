RESULT: PASS on items 1-3 and 5-7; item 4 PASS for the 6 declared changes, with 5 destructor statement changes that REPORT.md does not count. Package #4 hashes as announced (347/347 OK before and after) and holds exactly the 102 claimed T2 C/C++ verdicts (plus 3 copies of #193's theorem in other units); its 52 Gen modules are the pin's pin.lean byte for byte and their .olean files hold that text's elaboration; 91 claims keep their statements, #74/#338/#483 (retslot) and #130/#463/#549 (byval) change exactly by the declared shape, and the destructor claims #397, #499, #943, #973, #980 now let the destroyed object change (next3's endLifetime); every theorem depends only on propext, Classical.choice, Quot.sound; leanchecker accepts all 168 modules and --fresh VOEquiv.CheckAll102 (658 s); all 102 claims are class (i) in nmexp, p1exp and the three next3.1 checks.

# Check by an agent: re-check of package #4 t2_claims_next3_7c73739 at cirlean next3 7c73739 (veriforch, labelled, outside the pre-registrations)
An agent of the evidence-owner session. Check dir: this directory. Nothing was copied: lean and leanchecker read the sealed package in place
(LEAN_PATH = package lib + frozen next3 build ~/cirlean_frozen/next3_7c73739_20261030/.lake/build/lib/lean; the package names no other
root); every file written is in this directory (scripts, probes, outputs, five control .olean files of 2-14 KB). Record of inputs:
prereg/T/ADDENDUM_recheck_next3_veriforch.md, sha256 1d9b867edaa517aa27898f24405554dc6c362d73a1ff38d350d8b4c0ee48be90 (= the brief's).
Method of checks/n3pkg25-20261030T111132Z and t23next2-20261028T061053Z; claim list and original statements from
checks/t2-20261026T0321Z. Every script, lean and leanchecker run, scan and interpreter run went through pjobs_v3.py with coreh_guard_v2
(cmds_*.txt, pjobs_*.log, guard/), LEAN_NUM_THREADS=1, at most 8 Lean jobs at once, ulimit -v 32 GiB.

## 1. Hashes: PASS (sums/, out/w1_sums_before.out, out/w4_sums_after.out, pin/)
- Computed = announced: SHA256SUMS a1e24eae2fd185846a2d36f1d32559f6878da75b09b7eedf6494797a29a5605c, REPORT.md
  f7b43259f9e47fb18a1634124f30331115c009f5e7b453596d38a5831a322626; logs/build.log 6fd32341..., check_all_102.log 3e133c5b...,
  leanchecker_per_module.log 8539739c..., leanchecker_fresh.log b2e367dc... = REPORT.md's.
- sha256sum -c by absolute paths: 347/347 OK before the runs (2026-10-30T17:26:39Z) and after all of them (17:52:24Z). The package
  holds exactly the 347 listed files plus SHA256SUMS (348 files, 219 directories, no symlinks, no write bit); the list of type, mode,
  size and path is the same before and after. Size 3.88 GB, lib/ 3.76 GB.
- Pin: the frozen cir2lean 9c75efeada5522b4... = the manifest entry = the Gen table's copy; MANIFEST_build.sha256 8d2cc1ff96e4b41a...:
  1017/1017 OK before and after; the 201 .olean files under the frozen lib/lean (all LEAN_PATH reads besides the package) are manifest
  entries; it has no Gen/ or VO/ directory to shadow the package. lean bf8d54e4714cc4b0..., leanchecker 12c38901cdbfab17... (v4.35.0).

## 2. Claim set: PASS, 102 = 102 (tables/claims_orig.tsv, claim_theorems.tsv, pkg_modules.tsv; out/w1_claims.out)
- The claimed C/C++ verdicts of the original T2 runs (T2records/results.jsonl): 102 = 21 C proved, 74 C++ proved, 7 C++ partial (#54,
  #189, #193, #420, #463, #532, #858). Our independent recount (t2_outcomes_mine.tsv) and scans/jobs_t2_c.tsv give the same 102 orders
  and outcomes; the Gen table's 109 T2 rows are the same 102 claims.
- Their closures name 113 theorems. Each original module exists in its run's lean_ffab71e package, and each has a package module with
  the same unit and name: 112 distinct modules, because #499 and #980 share ~TJSONContext's theorem in the TJSONProtocol unit (runs
  protocol_w9 and protocol_w1).
- Missing: none. Added: no claim, and 3 theorems: Mutex::~Mutex (#193's function) also in the units TConcurrentClientSyncInfo,
  ThreadManager and TFileTransport. #193 was claimed in TServerSocket only (run transport_w7); the Gen table's roots_in.tsv lists it in
  all four units. So 115 VO modules = 112 + 3; CheckAll102 imports exactly these 115 and prints one theorem per module.

## 3. Gen: PASS (tables/gen_cmp.tsv, tables/gdig.tsv, gdig/, out/w1_gen.out)
- Gen table SHA256SUMS 6a50093481489b2c9381030755c797e50f80d4e63437b8616eb5c92a9afd323c (= announced): 1857/1857 entries OK. The 52
  package Gen sources are byte-identical (cmp) to w/T2_<unit>/pin.lean, whose hashes are the table's entries; the 52 units are the
  table's 52 T2 keys.
- The .olean files hold that text (new; nothing compiled to disk): per unit, one fresh process imported the package's Gen .olean and
  digested its constants (name, kind, Expr hash of type and value, universe parameters); a second elaborated pin.lean read from a pipe
  (lean --stdin, LEAN_PATH = frozen build only) and digested the constants it added. 52/52 equal (41,160 constants; per-constant lists
  identical for TOutput). This stands in for the build evidence that logs/build.log lacks (Findings, a).
- Classes: claims_detail.tsv's 109 T2 rows: 103 root same, signature same (======); 3 byval =C==== (#130, #463, #549) and 3 retslot
  ===C== (#74, #338, #483), signature changed; statement_changes.tsv lists the same six; units_final.tsv has 52 T2 units. This is
  REPORT.md section 1.

## 4. Statements (stmt/, tables/stmt_cmp.tsv, stmt_main_cmp.tsv; ax2/)
Method: each package theorem's statement (the <module>_spec block, proof opener removed, module path normalized) against the claim's
original module; and, in a fresh process per module, that source statement re-elaborated in a scratch namespace with the package
theorem (applied to its binders) as proof, against the stored type: Expr.equal for 115/115. Controls: with b + 0 < m.next for
b < m.next (definitionally equal) the statement type-checks and compares unequal; with .agg [.undef] for .agg [old] it fails to
type-check.
The 96 not regenerated: 91 claims identical. Of the 113 closure files 89 are byte-identical; 13 others differ in the proof only (a
local cir_exec attribute: #88, #150, #189, #409, #752; maxRecDepth: #413, #589, #814; rewritten tactics: #54, #194, #881, #981; 15
helper lemmas and a term-mode proof: #951). 5 claims differ, all destructors, from next3's endLifetime (a destructor call resets the
object to initVal; REPORT.md 2.3):
- #397 ThreadManager::~ThreadManager: the post `r = none ∧ m'.blocks b = m.blocks b ∧ Frame m m' []` becomes `r = none ∧ m'.blocks b
  = some ⟨k, true, .record "apache::thrift::concurrency::ThreadManager", .agg [.undef]⟩ ∧ Frame m m' [b]`.
- #499 TJSONContext::~TJSONContext (also in #980's closure; #980's root JSONPairContext::JSONPairContext is unchanged), #943
  TProtocolFactory::~TProtocolFactory, #973 AccessManager::~AccessManager: `r = none ∧ Frame m m' []` becomes `r = none ∧ Frame m m' [b]`.
Binders are unchanged in all five. The old statements said the call leaves the object unchanged; the new ones let it change (#397
gives its new value). REPORT.md section 1 classifies Gen, not statements, and does not count these five; section 2.3 names them only
in part and adds Mutex and IllegalStateException, whose claimed statements are unchanged (both already had Frame m m' [b]).
The 3 added Mutex::~Mutex theorems: TFileTransport's statement equals #193's; TConcurrentClientSyncInfo's (ip a Ptr, no hneed_empty
: True) and ThreadManager's (no hneed_empty, the object reset to .agg [.undef, .agg [.agg [.undef, .agg [.undef]]]]) differ.

The 6 regenerated: exactly the declared shape. REPORT.md's 12 quoted texts equal the files; 11 of its 12 quoted hashes are the files,
and #338's old hash 6683525a... is the t_d_generator copy of that file (runs compiler_w15 and _w8), equal to the claim's file
f12c3b34be50c261... up to the module path.
- retslot #74 getPath, #338 get_cpp_name, #483 get_documentation: every old binder unchanged; added br kr oldr, hbr : br < m.next,
  hkr : kr ≠ .readonly, hbrb : br ≠ b, hret : m.blocks br = some ⟨kr, true, .record "std::__cxx11::basic_string<...>", oldr⟩; the
  arguments gain .ptr (.loc br []); the post `(∃ g', r = some (.vec g' S)) ∧ Frame m m' []` becomes `r = none ∧ (∃ g', m'.blocks br =
  some ⟨kr, true, .record "std::__cxx11::basic_string<...>", .vec g' S⟩) ∧ Frame m m' [br]` (S = cs.map .int ++ [.int 0]): the same
  value, now in R, kind kept, and no other existing block changes.
  R must be a live block, a whole block (path []), of record type std::string, and not read-only. Not covered: a const result object
  (`const std::string p = s.getPath();`, an allocaConst block, as an agent found for D2), a result object that is a member or
  element of another object (a pointer with a non-empty path), storage of another type. hbrb (R is not *this) excludes nothing more:
  hobj and hret give b and br different record types.
- byval #130 TSocket::setPath: the argument .vec gp ((ps ++ [0]).map .int) becomes .ptr (.loc bp []), with bp kp, hbp : bp < m.next,
  hbpb : bp ≠ b, hpath : m.blocks bp = some ⟨kp, true, .record "std::__cxx11::basic_string<...>", .vec gp ((ps ++ [0]).map .int)⟩;
  the post is unchanged (Frame m m' [b]: the parameter object is not modified).
- byval #463 TConnection::setSocket: the argument .agg [.agg [.ptr sp, .agg [.ptr .null]]] becomes .ptr (.loc bs []), with hsrc
  giving bs exactly that value (record std::shared_ptr<apache::thrift::transport::TSocket>, null control block as before), hbs,
  hbsb : bs ≠ b; post unchanged.
- byval #549 t_delphi_generator::finalize_field: name, cls : Val become blocks bname, bcls with hname, hcls (live std::string blocks,
  any value, any kind, not required distinct); post r = none ∧ Frame m m' [] unchanged.
  The parameter hypotheses ask for a live whole block of the parameter's class holding the old argument value (#549: any value), of
  any kind; distinctness from *this follows from the types. They exclude argument objects of another type, dead ones and subobject
  pointers; the byval lowering passes a caller-allocated temporary.

## 5. Axioms: PASS (tables/axioms_summary.txt, ax_rows.tsv, axioms_print.tsv; ax2/, ax/ca_*.out, ax/ctlax.out)
- One fresh lean process per VO module (115) on the package's .olean files: every theorem in each module's constant list (3,457,
  auxiliary lemmas included) by Lean.collectAxioms is within {propext, Classical.choice, Quot.sound}; the 130 theorems named in the
  sources also by an own walk over the declarations through all imports, without the axiom records: records = walk 130/130, no constant
  missing. #print axioms: each of the 115 claimed theorems exactly [propext, Classical.choice, Quot.sound]; #951's 15 helper lemmas a
  subset. No error, warning or sorry line in any probe; all rc 0.
- In one environment (VOEquiv.CheckAll102): the cir_spec label's registry (Lean.labelled) holds exactly 115 theorems, the 115 that
  CheckAll102 prints, each on the three only, as are the 115 #print axioms lines. REPORT.md's list "(propext, Classical.choice,
  Quot.sound, Lean.ofReduceBool, Lean.trustCompiler)" is loose; no theorem uses the last two.
- Planted controls in the package setting: ctl_from_ax and ctl_indirect [ctl_ax]; ctl_sorry [sorryAx]; ctl_propext [propext];
  ctl_clean none; ctl_native [ctl_native._native.native_decide.ax_1_1] (Lean 4.35's native_decide adds its own axiom, so a test for
  Lean.ofReduceBool alone would miss it; the standard-three test does not); records = walk for each. A planted @[cir_spec] sorry
  theorem makes the label count 116 and shows [sorryAx].

## 6. Kernel replay: PASS (tables/leanchecker_plain.tsv, leanchecker_fresh.tsv; lc2/, fresh2/)
- leanchecker per module, read only: 168/168 (52 Gen, 115 VO, VOEquiv.CheckAll102) rc 0 with no output, 730 s in all (max 35 s); the
  .olean hashes are the package's SHA256SUMS entries.
- leanchecker --fresh VOEquiv.CheckAll102: rc 0, 657.9 s, no output, under ulimit -v 32 GiB (REPORT.md: 638 s). No write access was
  needed anywhere.
- Controls: BadCtl (a false theorem added with the kernel check skipped) rejected, rc 1; BadUse (imports BadCtl) accepted plain and
  rejected by --fresh (rc 1, "declaration type mismatch, 'badCtl'"); GoodCtl accepted plain and --fresh.

## 7. Exposure: all 102 class (i) (tables/exposure_t2.tsv, exposure_files.sha256; results files only)
- nmexp_pin7c73739 (gaps7/retslot pass order; SHA256SUMS 5ce3123d... = REPORT.md): 102 T2 claims, all (i): NOREACH 73, NOOP 24,
  MODELONLY 3 (#74, #338, #483: the closure reaches libstdc++'s basic_string copy constructor, which holds the op but runs as the model
  strCopyCtor), SPEC 2 (#858: hypothesis st ≠ 1; #193: every copy of the spec gives impl_ a null control block).
- p1exp_pin7c73739 (empty-store pointer check P1; SHA256SUMS 835bebd0... = REPORT.md): 102, all (i): LIVE 79, NODROP 22, NOREACH 1
  (#1000).
- next3.1 checks with T2 rows (universe A): n31exp_cscope, n31exp_cxxinvalid, n31exp_vachain: 102 each, all (i), NOREACH; no T2 claim
  in their exposed_*.tsv. claims_cscope.tsv and claims_vachain.tsv are byte-identical (2c376b0a...; the same generic reason).
  n31exp_b and n31exp_closures hold supporting data only. Each check's T2 claim set is the 102 orders.
- REPORT.md section 4 says closure_nm_funcs = 0 for all 109 T2 rows; claims_detail.tsv has 1 for #74, #338, #483 (the copy
  constructor above). Class (i) stands, by nmexp's MODELONLY rows.

## 8. Wording for the paper
Re-checked at cirlean next3 (7c73739), all 102 claimed C/C++ verdicts of T2 (95 proved, 7 partial) are proved again and kernel-checked
with only the standard axioms: 91 against statements identical to the claimed ones, 6 against statements regenerated for the new
lowering of by-value class parameters and returned class objects, and 5 against destructor statements whose frame now includes the
destroyed object. The re-proofs hold for next3's semantics and the pin's program terms, and where a statement changed they discharge a
different obligation: the regenerated return-value statements cover only result objects that are writable whole blocks of the returned
class, and the five destructor statements no longer state that the object is left unchanged.

## Findings on REPORT.md and the logs
(a) logs/build.log does not show the build REPORT.md section 3 states (52 Gen and 115 VO modules rc 0): it has 103 BUILD lines (102
VO modules and CheckAll102) and none for a Gen module; 12 failed (rc 1: ~ThreadManager, ~Mutex in ThreadManager,
t_go_generator::begin_types_declaration, t_map::get_val_type, t_list::get_elem_type, TUuid::operator=(TUuid&&), setConfiguration,
TOutput::operator(), ~IllegalStateException, ~t_generator_factory_impl<t_cl_generator>; rc 124 after 600 s: ~ProcessorGenerator,
finalize_field) with no later line, and 13 VO modules have no line. build_summary.log, guard_t2.log and the four empty Gen_*.log files
are from an earlier run at 12:01. Provenance is established here instead: the Gen .olean files by the digests (item 3), the VO
statements by re-elaboration against the .olean files (item 4), every .olean by leanchecker (item 6).
(b) Section 2.3 (destructors): item 4. (c) Section 4 (closure_nm_funcs): item 7. (d) #338's old hash: item 4. (e) Section 3's axiom
list: item 5.

## Deviations and limits
- First attempts that failed and were redone, outputs kept: lc.sh (lc/, fresh/: leanchecker found no lean on PATH, elan has no
  default; lc2.sh sets PATH); axrun.sh (ax/VO.*.out: the re-elaborated statement's proof was not applied to its binders, a type
  mismatch, STMT still equal; axrun2.sh); ctlax.sh's statement-control part (same cause; ctlstmt2.sh). Written, never run: stmt.sh
  (stmt2.sh), collect.sh (collect2.sh). stmt2.sh compared all theorem blocks of a file and so flagged #951 for its helper lemmas;
  stmt3.sh compares the <module>_spec statement only.
- awk warned "escape sequence \. treated as plain .": regexes passed with -v let "." match any character (wider matches, nothing missed).
- Bare shell: besides single-file reads, a few bare commands read 2-6 named small files at once (awk, ls, cmp), read only, no loops.
  The waits for the main wave were guarded jobs (waitdone.sh), one started from a Monitor.
- Not done: verifying the exposure checks' SHA256SUMS or reading their scripts (results files only); elaborating the original
  statements at ffab71e (text comparison); re-elaborating the VO proofs (leanchecker checks the .olean proofs). What R may be is read
  from the statements, not from a cirlean model of each caller.
- Identical statement text is the same Lean expression over next3's library and the pin's Gen; the semantics underneath changed (for
  example endLifetime and the retslot/byval lowering), so an unchanged statement can say something different about the program than
  at ffab71e.
- Core-h: 0.7976 over 367 guard logs up to 17:54:02Z (tables/coreh_final.txt), plus the final hashing job. Nothing external; no messages
  sent.
Written 2026-10-30T17:55:58Z (date -u) by an agent. SHA256SUMS covers every file here except itself; the final hashing job's own files (guard/w6_sums.log, out/w6_sums.out, pjobs_w6.*) are written while or after it runs and are not in it.
