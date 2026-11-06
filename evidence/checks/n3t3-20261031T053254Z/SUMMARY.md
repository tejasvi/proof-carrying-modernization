RESULT: PASS on items 1-3 and 6-8, with several of REPORT.md's accounts wrong (Findings). Package #3 hashes as announced (296/296 OK before and after) and holds exactly the 54 claimed T3 verdicts: 53 proved, and the TFileTransport destructor unfinished, now by a heartbeat timeout of its proof, no longer by the VTT lookup that made it undefined at ffab71e, e6ac99a and 424e821; the 46 Gen modules are the pin's pin.lean byte for byte and their .olean files hold that text's elaboration; 13 statements are byte-identical and 40 changed: the bool now passed (15; two of them also assume CtorInv, whose meaning differs at next3 through isAnyDiffRec), a typed-this hypothesis (24; within them buffer fields 2, a byte-array argument 2, getPath's result object 1, another translation unit 1) and another translation unit only (1); 15 claims carry a kernel-checked nonvacuity theorem, our evaluation finds an input on which both versions return for the other 32 that had a path at ffab71e, and 6 still relate no execution (the 5 trapping deleting destructors, setCurrentThreadHighPriority's unchanged argument count); every theorem depends only on propext, Classical.choice, Quot.sound; leanchecker accepts all 131 modules and --fresh VOEquiv.CheckAll54 (1179 s); all 54 claims are class (i) in nmexp, p1exp and the three next3.1 checks.

# Check by an agent: final check of package #3 t3_claims_next3_7c73739 (the 54 T3 verdicts at cirlean next3 7c73739; veriforch, labelled, outside the pre-registrations)
An agent of the evidence-owner session. Check dir: this directory (created 2026-10-31T05:32:54Z by mkdir with a date -u stamp). Nothing was
copied: lean and leanchecker read the sealed package in place (LEAN_PATH = package lib + frozen next3 build
~/cirlean_frozen/next3_7c73739_20261030/.lake/build/lib/lean); every file written is in this directory (scripts, probes, outputs,
four control .olean files of 2-14 KB), apart from my progress file under ~/.claude/jobs/progress (the user's checkpoint rule)
and drafts in the job's tmp directory. Record of inputs: prereg/T/ADDENDUM_recheck_next3_veriforch.md, sha256
1d9b867edaa517aa27898f24405554dc6c362d73a1ff38d350d8b4c0ee48be90 (= the brief's). Method of checks/n3t2-20261030T171447Z; claim
list and original statements from checks/t3-20261026T2147Z and its copy ~/fv_paper/replay/t3-20261026T2147Z; earlier vacuity
reasons from checks/vacuity-20261028T185625Z (and deep/), t3arity-20261028T200633Z, tier1-20261029T164912Z,
t1expo-20261029T172130Z, ctor-20261030T054550Z, n3kinds-20261030T050155Z. Every script, lean and leanchecker run, scan and
interpreter run went through pjobs_v3.py with coreh_guard_v2 (cmds_*.txt, pjobs_*.log, guard/), LEAN_NUM_THREADS=1, at most 8
Lean jobs at once, ulimit -v 32 GiB (bare-shell slips: Deviations).

## 1. Hashes: PASS (sums/, out/w1_sums_before.out, out/w4_sums_after.out, pin/)
- Computed = announced: SHA256SUMS 6400c13526692dfd5736cdcdc64798af5735120f354992119cac9d969cfa1ad6, REPORT.md
  b781f97b27f56d3f08f0fdc6eb3d456439f60b5d2a130ae89e9acf48b5614187; logs/build.log 04c02e03..., check_all_54.log 8ad96923...,
  leanchecker_per_module.log e7676a75..., leanchecker_fresh.log d51016de..., unfinished_TFileTransportD2Ev.log 84d4a9e6...
- sha256sum -c --strict by the absolute paths SHA256SUMS lists (296 well-formed entries, all inside the package): 296/296 OK before
  the runs (2026-10-31T05:42:18Z) and after all of them (06:24:01Z). The package holds exactly the 296 listed files plus SHA256SUMS
  (297 files, 113 directories, no symlinks, no write bit); the type/mode/size/path list and the log hashes are the same before and
  after. Size 1.70 GB (lib/ 1.65 GB).
- Pin: the frozen cir2lean 9c75efeada5522b4... = the manifest entry = the Gen table's copy; MANIFEST_build.sha256 8d2cc1ff96e4b41a...:
  1017/1017 OK before and after; the 201 .olean files under the frozen lib/lean (all LEAN_PATH reads besides the package) are
  manifest entries, and it has no Gen, VOEquiv, EquivLean or VerifOrch root that could shadow the package; worktree HEAD 7c73739c.
  lean bf8d54e4714cc4b0..., leanchecker 12c38901cdbfab17... (v4.35.0). Gen table SHA256SUMS 6a50093481489b2c...: 1857/1857 OK.

## 2. Claim set: PASS, 54 = 53 proved + 1 unfinished (tables/claims.tsv, checkall_imports.txt; out/w1_claims.out, unfinished_D2.out)
- The claimed verdicts: checks/t3-20261026T2147Z/outcomes/equivalent_list.tsv (sha256 654968c9...), 54 C++ equivalence verdicts
  in 13 commits (32, 50, 57, 58, 72, 77, 79, 89, 101, 105, 116, 138, 142). Each has a package source with the same module name
  (src/VOEquiv: 54 + CheckAll54); lib/VOEquiv has 53 .olean files + CheckAll54 (none for the unfinished one). CheckAll54 imports
  exactly the 53 and carries the 54th as a comment; it prints 131 theorems: 53 equivalent + 53 changed_only_where_old_unsafe + 15
  nonvacuous + the five TMemBufCtorInv lemmas of 072 and of 105. No package module outside the 54.
- The unfinished verdict, #142 TFileTransport::~TFileTransport (D2): its source is byte-identical to the T3 module (sha256
  567b10f3..., = REPORT.md section 5; this and the VTT pointer: 2 arguments for 2 parameters). The package log has an UNFINISHED
  line (rc=124 at 61 s, a wall limit) and error lines from another file, a scratch tf_hb50k.lean at maxHeartbeats 50000.
  Elaborating the package's own source (its maxHeartbeats 4000000) in a fresh process: rc 1 after 435.3 s; first error at l.16
  (equivalent), the same at l.24 (changed_only_where_old_unsafe): "(deterministic) timeout at `whnf`, maximum number of heartbeats
  (4000000) has been reached". #print axioms then says "does not depend on any axioms" for both failed theorems (as in the
  package log): in Lean 4.35 those lines alone do not show a proof.
- Not the obstacle of ffab71e, e6ac99a and 424e821. There the five VTT address points were .unknown "cir.vtt.address_point",
  undefined on every input before anything else ran (checks/vacuity-20261028T185625Z). At 7c73739 the D2 terms of both versions
  hold five .vttParamAddr ops and no .unknown (tables/d2_vtt_next3.tsv); Eval.lean l.1091-1094 evaluates them by Ctx.stride? over
  the VTT parameter (undefined only out of range). The obstacle now is the proof's cost: symbolic execution of the whole
  destructor body runs out of heartbeats. Whether this verdict would relate an execution is undecided here (body not traced; the
  unit's close, TOutput::printf and TOutput::perror have neither body nor model, tables/models_next3.tsv).

## 3. Gen: PASS (tables/gen_cmp.tsv, gdig.tsv, gdig/; out/w1_gen.out, w3j_gdigsum.out)
- The 46 package Gen sources are byte-identical (cmp) to w/T3_<order>_<old|new>_<TU>/pin.lean of the Gen table, whose hashes are
  its SHA256SUMS entries; the 46 keys are all of the table's T3 keys: 23 old/new pairs in 13 commits (#72 five units, #50 and
  #142 four each, the other ten one).
- The .olean files hold that text (nothing compiled to disk): per unit, one fresh process digested the constants of the
  package's Gen .olean (name, kind, Expr hashes of type and value, universe parameters), a second elaborated pin.lean read from a
  pipe (lean --stdin, LEAN_PATH = frozen build only) and digested the constants it added: 46/46 equal (27,546 constants), all rc 0.

## 4. Statements (stmt/, tables/stmt_cmp.tsv, stmt_classes_v2.tsv, stmt/residuals_v2.txt; ax/ STMT rows; bridge/, tables/defs_cmp.tsv)
Method: the blocks theorem equivalent, def WT and theorem changed_only_where_old_unsafe (and nonvacuous and the five lemmas
where present) of each package source against the claim's module in the T3 copy (runs/<order>_<new12>_cpp/lean_cert/VOEquiv),
byte for byte; namespaces are the same (VOEquiv.<module>) and the statements name no module path besides Gen units, so the
normalized comparison replaces every Gen unit's translation unit by <TU>. Each change was classified by its features and the
text left after removing them compared again (cls_v2.awk): no residual difference besides those listed below. In a fresh
process per module, every claimed statement was re-elaborated from the source text with the package theorem as proof:
Expr.equal with the stored type for 131/131 (53 equivalent, 53 changed_only_where_old_unsafe, 15 nonvacuous, 10 lemmas), and
the source WT with the stored value for 53/53. The statements' vocabulary is unchanged: EquivLean Core/Sim.lean (Equiv, Sim),
Bridge/Cir/Behaves.lean (Safe), Bridge/Cir/Obs.lean (ObsEq, EquivOn) and VerifOrch/Cir/Patch.lean (Bad, SafeRet) are
byte-identical to the T3 runs' equiv-lean b171660 and VerifOrch (tables/bridge_cmp.tsv). REPORT.md section 4's 40 quoted old and
new file hashes are those of the T3 copy's and the package's files (40/40).
- 13 unchanged, byte-identical files (the unfinished D2 too): #50 _setup_unixdomain_sockopts, TNonblockingServerTransport::listen
  and its D0; #58 THttpTransport D0; #72 TBufferBase D0, TVirtualTransport<TMemoryBuffer,TBufferBase> D0, THttpTransport D0,
  TMemoryBuffer open, close and isOpen, TFramedTransport and TBufferedTransport borrowSlow; #142 setCurrentThreadHighPriority.
  The same text now speaks about next3's semantics and the pin's terms.
- 40 changed, by kind (counts of claims; a claim can have more than one):
  (a) bool parameter now passed, 15: the 11 TEvhttpServer::complete, breakLoop, setNoDelay, setKeepAlive, setLinger (setLinger
      renames its int x1 -> x2). The binder (x : Bool) is added and the argument list gains .bool x, in equivalent and in WT. The
      old statements passed one argument fewer than the function has parameters, so both calls went wrong at argument binding
      and the old theorems related no execution; the new ones are different statements, now with content, and exclude nothing.
      Each of the 15 adds `theorem nonvacuous` (item 5). The 13 without CtorInv are the texts of the earlier re-proofs (tier-1
      c17690c for the 9 complete and breakLoop, tier-0 424e821 for the three setters; out/w3i_priorstmt2.out).
  (b) CtorInv, 2 (072, 105; with (a)): hypothesis (hctor : CtorInv x1 m), also in WT, plus five lemmas on TMemBufCtorInv over the
      old unit. All nine blocks are the texts of the companion ctor package (c17690c, checked in checks/ctor-20261030T054550Z;
      out/w3g_ctorstmt.out), and the texts of CtorInv and of the predicates it uses are unchanged, but one of them, isAnyDiffRec,
      lists 10 more record names at next3 (anon.0, std::string, TException and TTransportException with their .base records,
      std::_Nocopy_types, std::_Any_data, std::_Function_base, std::function<void (bool)>). Blocks of those types are no longer
      "MbufFree": the closure condition no longer constrains them, while the request pointer's target, the buffer's bytes and
      every MbufFree block may no longer point to them. So CtorInv is a different bound from the one an agent read (weaker for
      those blocks, stronger for pointers into them). Against the T3 statement: weaker (a hypothesis).
  (c) typed this, 24: (hx0_ty : ∀ b p blk, x0 = Ptr.loc b p → m.blocks b = some blk → blk.ty = .record "<class>" ∧ p = []), also
      in WT: if `this` points into a block, that block is a whole object of exactly the method's class. Weaker. It excludes calls
      on the base-class part of an object of a derived class (a base pointer carries the base's path, Eval.lean l.1054-1059), on
      an object that is a member or element of another object (in-place storage such as make_shared's too), and on storage of
      any other type. For TBufferBase::setReadBuffer and setWriteBuffer it excludes every object the program can create:
      TBufferBase is abstract (pure virtual slots, checks/vacuity-20261028T185625Z) and exists only as a base-class part.
      Classes: TNonblockingServer 6 getters; TNonblockingServerSocket 12 (getters, setters, isUnixDomainSocket, getPath);
      TMemoryBuffer 2; THttpClient 2 (#72, #77); TBufferBase 2. Within (c):
      - buffer fields, 2 (available_read, available_write): rBase_ and wBase_ (paths [0,0,1], [0,0,3]), when they point into a
        block, point into a u8 array, and below m.next. Further excludes buffer pointers into other storage.
      - byte-array argument, 2 (setReadBuffer, setWriteBuffer): (hx1_ty) the buffer argument, when it points into a block, points
        into a u8 array. Further excludes buffers of other types (arrays inside objects, other element types).
      - result object, 1 (#50 getPath, the retslot shape): the call gains x1 : Ptr, the caller's result object, with a bound and
        (hx1_ty) a whole std::string block; the result is observed in memory (ObsEq on the blocks below m.next) instead of as the
        return value. A different statement; excludes result objects that are not whole std::string objects.
      - another translation unit, 1 (getSocketFD): TNonblockingSSLServerSocket's terms -> TNonblockingServerSocket's.
  (d) another translation unit only, 1 (#50 TTransport::getMaxMessageSize): the same text over PeekProcessor's terms instead of
      TZlibTransport's; no hypothesis added. The T3 record's verdict is per function (its prepass lists the inline function under
      15 translation units); the module in the T3 copy came from TZlibTransport, and both TU changes follow the claim list's TU
      column, as the Gen table does. Different program terms of the same source function.
  Not found: a change of WT or domain other than the hypotheses above (the WT changes mirror those of equivalent in all 40), a
  changed conclusion, a destructor frame change (the T3 statements have no frame clause; at next3 evalCall applies endLifetime
  to destructors, Eval.lean l.2034, under the unchanged D0 statements, whose bodies trap first).

## 5. Non-vacuity at next3 (tables/claims_class.tsv, claims_final.tsv, witness_final.tsv, arity_next3.tsv, models_next3.tsv, mrelease_next3.tsv; wit/)
"Relates an execution" = some input of the statement's domain on which both versions are safe (Equiv is Sim both ways, Sim
assumes Safe; EquivOn's Bad = not WT or the old version not SafeRet). Over the 53 proved claims: relates some execution 47 (15 by
a package theorem, 32 by our evaluation), relates none 6, undecided 0.
- Package theorem, 15 (the 11 complete, breakLoop, setNoDelay, setKeepAlive, setLinger): `theorem nonvacuous : ∃ args m, WT args
  m ∧ Safe (evalCall <new> ..) ∧ Safe (evalCall <old> ..)`, re-elaborated against the stored type and kernel-replayed (item 7).
  - complete (11; the dropped bool and evhttp_add_header without a model at ffab71e, the shared_ptr counter read at e6ac99a,
    424e821 and c17690c): the bool is passed and the libevent functions have models at 7c73739; the witness is the tier-1
    memory (mkCompleteWitnessMem, text unchanged), whose shared pointers have no control block. The counter read is still there
    (_M_release: bitcast s32* -> s64*, 64-bit load, in every unit) and undefined at next3 (checks/n3kinds-20261030T050155Z,
    K13): with obuf given a control block as RequestContext's constructor makes it (heap _Sp_counted_ptr<TMemoryBuffer*>,
    counts 1/1), complete goes wrong in both versions with "type-punned access" (wit/CB2_32.out, CB2_72.out; the unmodified
    witness returns). RequestContext's constructors (C1 and C2) still call evbuffer_pullup, which has no model (#32 new unit, Gen
    l.2443, l.2893). So the 11 relate only executions on request contexts without control blocks (072 and 105: within CtorInv).
  - breakLoop (the bool; TOutput::instance and pthread_self without models at ffab71e): pthread_self and event_base_loopbreak have
    models; the witness takes error = false with threadId_ = pthread_self's 1 and a null event base; breakLoop(true) is never .ok
    (the package's evalCall_breakLoop_true_not_ok), and the notify path reaches poll, which has no model (my generic witness).
  - setNoDelay, setKeepAlive, setLinger (the bool): the witness has socket_ = -1 and returns early; setsockopt still has neither
    body nor model, so every execution that reaches it goes wrong (my generic witnesses with socket_ = 0).
- Our evaluation, 32 (the 32 that had a path to a normal return at ffab71e: the 24 typed-this claims, getMaxMessageSize and the 7
  unchanged #50/#72 functions): a memory built for the statement (a whole object of the method's class for `this`, every field
  defined, one shared heap byte array behind every uint8_t*, fresh objects behind other pointers, std::string objects as the empty
  string, integer arguments 4), under the new unit's layout and again under the old's; evalCallIter (10,000 steps) of both
  versions returns in every case (wit/W_*.out; W3_22 and W3_23 for the two std::string users). The object's class equals the
  hypothesis' class in all 24 typed-this claims. This is evaluation evidence, not a kernel-checked theorem. Two of them,
  setReadBuffer and setWriteBuffer, relate executions only on memory that holds a whole TBufferBase object, which no C++ program
  creates.
- Relates none, 6, with the earlier reason unchanged at 7c73739: the 5 deleting destructors of abstract classes (#50, #58, #72 x3:
  alloca; try { store; load; trap } in both versions; .trap is .ub "trap", Eval.lean l.1889; my evaluation gives that UB), and
  #142 setCurrentThreadHighPriority, whose unchanged statement still passes 1 argument for 2 parameters (bindArgs gives "block
  argument count mismatch", Basic.lean l.157-167, Eval.lean l.1690-1695; my evaluation gives that UB). Its other earlier reason
  is gone: sched_get_priority_max/min, pthread_self and pthread_setschedparam have models at 7c73739.
- The 22 earlier vacuous verdicts: 15 now relate an execution (package theorem), 6 still none, and the TFileTransport destructor
  is unfinished (no theorem; the VTT lookup is no longer its obstacle; undecided). The 12 tier-1 verdicts (complete, breakLoop) all
  relate an execution by a package theorem, with the control-block limit above for complete.

## 6. Axioms: PASS (tables/axioms_probe.tsv, print_axioms.tsv; ax/, ax/ctlax.out; out/w2_chk54.out, w1_scan.out)
- One fresh lean process per VOEquiv claim module (53) on the package's .olean files: every theorem in each module's constant
  list (1,139, auxiliary lemmas included) by Lean.collectAxioms (Lean 4.35 reads the axiom records each .olean stored) is within
  {propext, Classical.choice, Quot.sound}; the 258 theorems named in the sources also by my own walk over the declarations through
  all imports, without the records: records = walk 258/258, no constant missing. #print axioms: each of the 131 claimed theorems
  exactly [propext, Classical.choice, Quot.sound]; of all 258 source theorems 224 the three, 25 [propext], 9 none. No error,
  warning or sorry line in any probe; all rc 0.
- The package's own CheckAll54.lean re-elaborated in a fresh process: rc 0, its 393 output lines byte-identical to
  logs/check_all_54.log; 131 "depends on axioms" entries, each exactly the three, no sorryAx.
- Planted controls in the package setting (CtlAx imported with a package module): ctl_from_ax and ctl_indirect [ctl_ax];
  ctl_sorry and a probe-local sorry theorem [sorryAx]; ctl_propext [propext]; ctl_clean none; ctl_native its auxiliary axiom
  ctl_native._native.native_decide.ax_1_1; a theorem using the package's getPath equivalent the three; records = walk for each.
- Source scan of all 132 package .lean files (tables/scan_counts.tsv; the planted file hit all 12 patterns it holds): no sorry,
  admit, axiom, native_decide, ofReduceBool, debug option, implemented_by, extern, #exit or run_cmd. Other hits: "unsafe" and
  "opaque" only in comments and strings; addDecl in Loops.lean's cir_name_functional% (byte-identical to the T3 equiv-lean, the
  declarations go through the kernel); "initialize" in Gen demangled names; CIR.Logic.Kernel imported by the 15 modules with
  nonvacuous (decide +kernel).

## 7. Kernel replay: PASS (tables/leanchecker_plain.tsv, leanchecker_fresh_and_controls.tsv; lc/, fresh/)
- leanchecker per module, read only, LEAN_PATH = package lib + frozen next3 build: 131/131 (46 Gen, 28 EquivLean, 3 VerifOrch, 53
  VOEquiv, CheckAll54) rc 0 with no output, 1268 s in all (max 106 s); the 131 .olean hashes are the package's SHA256SUMS
  entries.
- leanchecker --fresh VOEquiv.CheckAll54 (the closure of the 53 from an empty environment): rc 0, 1179.0 s, no output, under
  ulimit -v 32 GiB (the package's log: 1152 s). No write access was needed anywhere.
- Controls: BadCtl (a false theorem added with the kernel check skipped) rejected, rc 1 ("declaration type mismatch, 'badCtl'");
  BadUse (imports BadCtl) accepted plain and rejected by --fresh (rc 1, 63 s); GoodCtl accepted plain and --fresh (36 s).

## 8. Exposure: all 54 class (i) (tables/exposure_t3.tsv, exposure_files.sha256; results files only)
- nmexp_pin7c73739 (SHA256SUMS 5ce3123d... = REPORT.md): 54 T3 rows = my 54, all (i): NOREACH 50, MODELONLY 4 (getPath and the
  three TSocket setters).
- p1exp_pin7c73739 (SHA256SUMS 835bebd0... = REPORT.md): 54, all (i), LIVE.
- next3.1 checks mutant/n31exp_cscope, _cxxinvalid, _vachain: 54 T3 rows each (universe A), all (i), NOREACH; no T3 claim in their
  exposed_*.tsv (cscope's and vachain's are empty). n31exp_b and n31exp_closures hold supporting data only.

## 9. Wording for the paper
At the third revision of the semantics (cirlean 7c73739), 53 of the 54 equivalence verdicts are proved again and pass the same
axiom and replay checks; the proof for the destructor of \code{TFileTransport}, whose lookups in the table of virtual-table
pointers this revision supports, runs out of its time budget. Thirteen statements are unchanged; of the other 40, 15 now pass the
missing \code{bool} (two of them with the hypothesis on the request context of the companion re-proof), 24 assume that the object
a method is called on is a whole object of the method's class, which leaves out calls on the base-class part of an object and,
for the abstract class \code{TBufferBase}, every object the program creates, and one uses the program terms of another
translation unit. Fifteen of the 53 come with a theorem that some input runs without undefined behaviour in both versions, our
evaluation finds such an input for 32 more, and 6 still relate no execution, the five deleting destructors and
\code{setCurrentThreadHighPriority}, whose unchanged statement still leaves out its \code{bool}; the verdicts for \code{complete}
still relate only request contexts without control blocks.

## Findings on REPORT.md and the logs
(a) Section 1: the 46 Gen units are 23 old/new pairs in 13 commits, not 11 (tables/gen_cmp.tsv).
(b) Section 1, "28 TypedThis" claims: typed-this hypotheses are in 24 claims (23 plus getPath, which REPORT.md counts as the retslot
    claim); its 28 also count getMaxMessageSize (another translation unit only) and breakLoop, setNoDelay, setKeepAlive and
    setLinger (the bool only). The translation-unit change of getMaxMessageSize (TZlibTransport -> PeekProcessor) is not
    mentioned; that of getSocketFD is.
(c) Section 1, the 11 complete verdicts "proved under CompletePre x0 x1 x2 m" and "CompletePreCtor": no CompletePre occurs in any
    package source (out/w3b_names.out). Nine statements are T3's plus the bool, with no hypothesis; 072 and 105 add CtorInv x1 m.
(d) Section 3: nmexp has 4 MODELONLY T3 rows (getPath and the three TSocket setters), not getPath alone. Class (i) stands.
(e) Section 5: the quoted error lines are from a scratch file (tf_hb50k.lean, maxHeartbeats 50000) and the UNFINISHED line is a
    61 s wall limit; the module's own source, at 4000000 heartbeats, fails the same way after 435 s (item 2).
(f) logs/build.log is sorted by module name, not written in build order (CheckAll54 comes before the modules it imports);
    provenance is established here by the Gen digests (item 3), the statement re-elaboration (item 4) and leanchecker (item 7).
(g) The package log and my run both show #print axioms reporting "does not depend on any axioms" for the two theorems whose proofs
    timed out; the 131 lines of CheckAll54 come from modules that compiled and replay.

## Deviations and limits
- Rule slips, all read-only or writing only my own files: before 05:41:58Z one bare command began with `cd .../scripts` (no
  effect, absolute paths) and wrote scripts/scan_v2.sh by awk from scan.sh; one bare recursive grep over the frozen CIR/ and the
  package's src/ for helper definitions (a multi-file scan outside a guarded job); two bare for-loops (two iterations each) wrote
  wit/CB_32.lean, CB_72.lean and wit/CB2_32.lean, CB2_72.lean; several bare awk, ls and cmp commands read 2-4 named files or
  directories at once (memory notes, earlier checks' SUMMARY files, my own outputs); one bare sed (no -i) shortened paths in a
  3-file listing. Several scripts and templates were written by bare awk from earlier versions of mine (scan_v2.sh, cls_v2.*,
  gen_wit_v2.sh, wit_lib_v2.lean.tmpl, prior_stmt_cmp_v2.sh, collect_v2/v3.sh, final_table_v2.sh).
- Superseded, kept (no rm): scan.sh (never run); cls.sh (ran; its residual dump was truncated by `>`, cls_v2); gen_wit.sh and
  wit_lib.lean.tmpl (never run; v2 evaluates 10,000 steps); scripts/wit_lib_v3_draft.txt (a broken awk splice, never used);
  wit/CB_32.lean and CB_72.lean (drafts with a placeholder #eval, never run; CB2_*); prior_stmt_cmp.sh (ran with a wrong column,
  no output; v2); collect.sh (ran before the fresh replay ended; its axiom table failed on an awk array clash; collect_v3);
  final_table.sh (never run; v2 reads witness_final.tsv). Faulty lines kept in outputs: claims.sh's "package modules not among
  the claims" list (it split a space-separated file on tabs; the counts are right), stmt.sh's nonvacuous column (read from the ax/
  STMT rows instead), gdigsum.sh's time sums (wrong columns; olean 38 s, stdin 449 s), report_hashes.sh's "changed claims not in
  REPORT section 4" count (compared indices with keys; its list of the 14 not listed is right).
- Evaluation witnesses (item 5) are #eval runs of evalCallIter (Lean's interpreter; memory operations run through their
  implemented_by runtime versions), not kernel-checked theorems; their memories meet the statements' hypotheses by construction
  and the this-class check, not by a Lean proof of WT.
- Statements were compared as text with the T3 modules (not elaborated at ffab71e). What the hypotheses exclude is read from the
  statements and the semantics, not from a model of each caller. Identical statement text is a Lean expression over next3's
  library and the pin's Gen: an unchanged statement can say something different about the program than at ffab71e.
- Not done: verifying the exposure checks' own SHA256SUMS or scripts (results files only); re-elaborating the VO proofs
  (leanchecker checks the .olean proofs); tracing the unfinished D2 body.
- Core-h: 1.0040 over 325 guard logs up to 06:24:21Z (tables/coreh.txt), plus the core-hour and final hashing jobs. Nothing
  external; no messages sent.
Written 2026-10-31T06:26:09Z (date -u) by an agent. SHA256SUMS covers every file here except itself; the final hashing job's own files (guard/w9_sums.log, out/w9_sums.out, pjobs_w9.log) are written while or after it runs and are not in it.
