RESULT: (1) PASS hashes: SHA256SUMS 5c737e34... = announced, 77/77 OK before and after, cp -rL copy with 0 symlinks 77/77 OK; (2) PASS statements, with one added bound: equivalent / changed_only_where_old_unsafe / nonvacuous have the type of the T3 statement plus the bool, with the single added hypothesis CtorInv x1 m (WT = WT_tier1 ∧ CtorInv, WT_tier1 = the tier-1 WT; Lean examples in fresh processes, 10 negative controls per module fail); CtorInv fixes the RequestContext block, obuf's rBase_/wBase_ into a live heap byte array of free size, the request pointer's target only up to a type class (not evhttp_request), and both _M_pi to null or a live _Sp_counted_ptr<TMemoryBuffer*> block of free contents, plus a closure condition on the whole memory; (3) the five TMemBufCtorInv lemmas are proved for the OLD unit of each pair only (105's new unit: the generic lemmas apply through hctx_tmembuf_new; 072's new unit: HasTMemBufOpsCtx is false, layout); the four preservation lemmas start from pre-states stronger than TMemBufCtorInv and conclude only TMemBufCtorInv, so they do not chain; TMemBufCtorInv is the conjunct CtorInv uses; no lemma establishes the rest of CtorInv, and the program does not reach it: RequestContext's constructor is UB in all four units (evbuffer_pullup, no model; process calls C1, no body), the obuf part (TMemoryBuffer() -> initCommon(null, 1024)) does give TMemBufCtorInv, and the control block that shared_ptr(T*) makes is admitted by CtorInv and makes complete UB in both versions; (4) PASS axioms: all 2722 theorem constants of the 29 modules within {propext, Classical.choice, Quot.sound}, by the per-olean records and by a records-free walk over the bodies; verdict theorems exactly the three; planted controls fire; (5) PASS kernel replay: leanchecker 29/29 modules rc 0 and --fresh VOEquiv.CheckAll2 rc 0 (318 s) in my copy; a planted ill-typed olean is rejected; (6) PASS Gen: the 4 Gen modules (.lean and .olean) are byte-identical to the tier-1 package's, nothing to classify; (7) the witness satisfies CtorInv, has null control blocks (and a null ibuf), returns in both versions of both pairs and passes evhttp_add_header and evhttp_send_reply; (8) evalCall_M_release_ub states the UB of _M_release's 64-bit load under a punned-load hypothesis that spPtrValid_of_spBasePtrInv discharges for live _Sp_counted_ptr<TMemoryBuffer*> blocks; with evalCall_uptr_dtor this gives REPORT section 2 within CtorInv (no single package theorem states it); evaluations agree. So on states with program-made control blocks the theorems relate UB to UB, and every .ok execution they relate has null control blocks, which no constructor in the units creates.

# Check by an agent: check of veriforch's companion package t3_extmodels_072_105_ctor_c17690c (072 and 105 under CtorInv; post-freeze, exploratory)
Written 2026-10-30T06:21:57Z (date -u). Check dir: this directory. Copy: ~/fv_paper/replay/ctor-20261030T054550Z (pkg/ = cp -rL of the
package; probe/ = my probe files; ctl/ = leanchecker control modules). Package: ~/veriforch/runs/postfreeze/
t3_extmodels_072_105_ctor_c17690c (producer the orchestrator session). Tier-1 package: ~/veriforch/runs/postfreeze/t3_extmodels_c17690c.
cirlean: frozen worktree ~/cirlean_frozen/extmodels_c17690c_20261028 and its build. Method and wording follow
checks/tier1-20261029T164912Z; probe sources are also copied to probe_src/.

## 1. Package and copy: PASS (sums_before.txt, sums_after.txt, pkg_check_*.txt, copy_check_*.txt, tier1_check_*.txt)
- SHA256SUMS sha256 5c737e348a650340cbe8459cbebdc77a6810f3e4ec19fa1040539f99e64d32f6 = announced (77 lines); REPORT.md
  3bdd7e92cf230504186e6cd53e1f1f3b6123e8167c1b8266ba2f61ecfddaccb3 and leanchecker_replay.log
  1631bd418be3db29a33a59fa005225506a14d6904d0976040e7e687c4e1562b1 = announced (all computed with sha256sum).
- sha256sum -c by absolute paths (no cd): 77/77 OK before (05:51:17Z) and after all runs (06:17:00Z). Copy: cp -rL, 0 symlinks,
  78 files, 77/77 OK both times. Tier-1 package: SHA256SUMS 3ab57abc5bbfdfc085e7d2244fd6bddbd1c81de9a17d902f7babc8f281e74194,
  131/131 OK before and after.
- Frozen cirlean: HEAD c17690c99039b2621955ad1b3296e3b6b24798d9, no partial-clone or promisor config, 0 tracked changes, before
  and after (GIT_ALLOW_PROTOCOL=file). Nothing was written in the package, the tier-1 package or the frozen tree; nothing was
  chmod-ed.

## 2. Statements (probe_P_stmt_072.out, probe_P_stmt_105.out, probe_P_neg_*.out, stmt_compare_v2.txt; scripts/gen_probes.py)
- Fresh lean processes, LEAN_PATH = copy lib + frozen c17690c build. #print of WT, WT_tier1, CtorInv, TMemBufCtorInv,
  SpBasePtrInv, MbufFreeClosed, isMbufFreeBlock, IsMbufFreeTy, isProtectedOrWrapperTy, isAnyDiffRec, noDiffTy, mkTMemBufValAt,
  Bad, EquivOn, ObsEq, Equiv, Sim; the printed bodies equal the sources.
  WT_tier1 = fun args m => ∃ x0 x1 x2, args = [.ptr x0, .ptr x1, .bool x2] ∧ (∀ b p, x0 = Ptr.loc b p → b < m.next) ∧
             (∀ b p, x1 = Ptr.loc b p → b < m.next);   WT = the same with "∧ CtorInv x1 m" appended.
- 'example' checks, 0 errors in both modules:
  E1 equivalent : ∀ (x0 x1 : Ptr) (x2 : Bool) (m : Mem) (hx0) (hx1) (hctor : CtorInv x1 m), Equiv (ObsEq m) (evalCall <new>
     ... [.ptr x0, .ptr x1, .bool x2] m) (evalCall <old> ...): the T3 statement (replay t3-20261026T2147Z, runs/<order>_*/
     lean_cert/VOEquiv) with the bool and the hypothesis CtorInv added; the conclusion is the T3 one plus the bool.
  E2 changed_only_where_old_unsafe : EquivOn (Bad (T3 WT + bool + CtorInv) <old>) <new> <old>.
  E3 WT = T3 WT + bool + CtorInv (rfl). E4 WT_tier1 = T3 WT + bool (rfl); its text equals the tier-1 package's WT (normalized).
  E5 nonvacuous : ∃ args m, WT args m ∧ Safe (evalCall <new> ...) ∧ Safe (evalCall <old> ...).
  E8 ctx_old / ctx_new are the old / new unit's ctx (rfl). Text: the package's equivalent is the T3 text plus "(x2 : Bool)",
     ".bool x2" and "(hctor : CtorInv x1 m)"; changed_only_where_old_unsafe's text is the T3 text (stmt_compare_v2.txt).
- Negative controls, each failing with "Type mismatch" at its own line in both modules: NEG1 the tier-1 statement (no CtorInv)
  := equivalent; NEG2 WT = tier-1 WT (rfl); NEG3 Bad with the tier-1 WT := changed_only_where_old_unsafe; NEG4 the T3 statement
  without the bool; NEG5 WT_tier1 = WT; NEG6.0-6.4 the five lemmas restated over the new unit.
- What CtorInv x1 m constrains (CompleteCtorCongr.lean l.59-91, MbufFreeModels.lean l.10-71):
  - MbufFreeClosed m: no block at or above m.next, and every block (stack blocks included) whose type is "MbufFree" holds only
    pointers into non-stack blocks of MbufFree types. MbufFree = no isAnyDiffRec record by value (anon_struct.5/.6 = the vtable
    records, TBufferBase(.base), TVirtualTransport<TMemoryBuffer,TBufferBase>(.base), TMemoryBuffer) and not "protected"
    (RequestContext, TMemoryBuffer, _Sp_counted_ptr<TMemoryBuffer*>, _Sp_counted_base, unique_ptr<RequestContext>,
    anon_struct.1-4/.7, byte arrays u8[n], pointer, bool and integer scalars).
  - x1 = .loc b_rctx [], b_rctx < m.next a live heap block of record type RequestContext.
  - field 0 (req) = a .loc pointer, any path, into a non-stack block of an MbufFree type.
  - field [2,0,0] (obuf._M_ptr) = .loc b_mbuf [] with TMemBufCtorInv m b_mbuf: b_mbuf a live heap TMemoryBuffer block, and a
    live heap block b_buf of type u8[n_buf] holding .arr vs_buf (its pointers into MbufFree blocks) with rBase_ ([0,0,1]) =
    (b_buf,[rOff]) and wBase_ ([0,0,3]) = (b_buf,[wOff]), rOff ≤ vs_buf.length, wOff ≤ vs_buf.length.
  - fields [1,0,1,0] and [2,0,1,0] (ibuf._M_pi, obuf._M_pi): each null, or (b_sp,[0]) with b_sp < m.next a live heap block of
    record type _Sp_counted_ptr<TMemoryBuffer *, _S_atomic>.
- What it leaves free: ibuf._M_ptr; the control blocks' contents (vptr, counts, owned pointer: a protected type, outside the
  closure); every TMemoryBuffer field but rBase_ and wBase_ (vptr, configuration, message-size counters, rBound_, wBound_,
  buffer_, bufferSize_, maxBufferSize_, owner_) and whether the value has the unit's TMemoryBuffer layout; the byte array's size
  n_buf (not tied to vs_buf.length, bufferSize_ or wBound_; the type u8[...] is fixed, the size is not); the order of rOff and
  wOff; the request block's record type and layout (evhttp_request is not named), its connection and its header lists (evkeyvalq
  is not named; those blocks are constrained only through the closure). The libevent models report UB where these are wrong.
- So _M_pi is constrained, the control blocks are not. CtorInv is the only change to the obligation and acts as a bound on the
  memories the theorems cover; it excludes the tier-1 counterexample memories (section 7).

## 3. The TMemBufCtorInv lemmas (probe_P_stmt_*.out E6/E9/E10, probe_P_neg_*.out NEG6, probe_P_t072new_v2.out, probe_P_wit.out)
- Statements (#check; restated in E9 with the old unit's Gen ctx written out, type-checks; NEG6 with the new unit's, fails):
  initCommon_establishes_TMemBufCtorInv: from a well-formed m with b_mbuf < m.next a live heap TMemoryBuffer block holding
  mkTMemBufValAt <any field values> (six members), initCommon(this, null, n, true, wOff) with 2 ≤ n ≤ 4294967295 and wOff ≤ n
  returns and TMemBufCtorInv m' b_mbuf holds after. write / read / borrow / consume_preserves: on the in-buffer path only
  (write: wOff + k ≤ n_buf; read: rOff + k ≤ rbOff; borrow: req_len ≤ rbOff - rOff; consume: rOff + k ≤ rbOff), from a
  pre-state with the mkTMemBufValAt shape and rBase_, rBound_, wBase_ in one heap byte array (write: also wBound_ = (b_buf,
  [n_buf]) and vs_buf.length = n_buf; read, borrow, consume: wBound_ free; read, consume: k ≤ remainingMessageSize_ ≤ 2^63-1;
  borrow: *len a stack u32), the call returns (read: k; borrow: (b_buf,[rOff])) and
  TMemBufCtorInv m' b_mbuf holds. REPORT section 1 describes more than the statements give: the block m.next + 6, the offsets 0
  and wOff, the advanced rBase_/wBase_ are in the proofs, not in the statements. Slow paths (writeSlow, readSlow, borrowSlow:
  virtual calls; realloc in ensureCanWrite) are not covered.
- Units: every instance in O072 and O105 is over evalCall ctx_old, the old unit of each pair (d10129d4, 9c7c8e6e).
  - 105 new (7a3e7bd1): O105 proves HasTMemBufOpsCtx ctx_new (hctx_tmembuf_new) without instantiating the lemmas; the generic
    TestTMemBufOps.evalCall_*_TMemBufCtorInv applied to it type-check (E10.0-10.4), so the five statements hold there too.
  - 072 new (c98e79ad): HasTMemBufOpsCtx is false. The new TBufferBase gains a bool and a 7-byte pad, which shifts
    TMemoryBuffer's members (new: [1] u8[7], [2] buffer_, [3] bufferSize_, [4] maxBufferSize_, [5] owner_; old: [1] buffer_,
    [2] bufferSize_, [3] maxBufferSize_, [4] owner_). ta_buf, ta_bufSize and ta_owner fail (typeAt values printed), initCommon's
    and read's bodies do not match mkInitCommonBody / mkReadBody, and mkTMemBufValAt's six-member value cannot describe the new
    layout. No lemma covers 072's new unit.
- Same predicate: CtorInv contains TMemBufCtorInv m b_mbuf (the constant TestCompleteCongr.TMemBufCtorInv) as a conjunct, for
  the block obuf._M_ptr points to (E6: CtorInv x1 m → ∃ b_rctx v_rctx b_mbuf, ... ∧ TMemBufCtorInv m b_mbuf, type-checks); the
  lemma conclusions use the same constant (E9). The converse does not hold: TMemBufCtorInv says nothing of MbufFreeClosed, the
  RequestContext block, the request pointer or the control blocks.
- The conclusions (returns ∧ TMemBufCtorInv) are weaker than every lemma's pre-state (rBound_, wBound_ and the value's shape are
  not restated), so no conclusion discharges another lemma's hypotheses: a sequence such as initCommon then write is not covered
  by these statements.
- Gaps between "the program establishes it" and the WT used:
  (a) Only the TMemBufCtorInv conjunct has lemmas; MbufFreeClosed, the RequestContext and request conjuncts and SpBasePtrInv have
      none, and no lemma relates CtorInv to a state that a program path produces.
  (b) The program's RequestContext constructor is UB in these terms (G1, G2). RequestContext::RequestContext (C2) calls
      evbuffer_pullup (EVBUFFER_DATA, for ibuf) before obuf is built; evbuffer_pullup has neither body nor model ("call to an
      external function without a model: evbuffer_pullup", all four units). TEvhttpServer::process calls the complete-object
      symbol C1, which has neither body nor model (072-old Gen Unit.lean l.2612-2622; UB at that call in both old units). So no
      execution of the program in these terms creates the RequestContext that complete receives.
  (c) The obuf part works. TMemoryBuffer::TMemoryBuffer(shared_ptr<TConfiguration>) calls initCommon(this, nullptr, 1024, true, 0)
      (072-old Gen l.2541-2575). Evaluated on a heap TMemoryBuffer block (as operator new and the first cast leave it) with a null
      configuration, it returns in all four units (G3). In 072-old the result has rBase_ = rBound_ = wBase_ = buffer_ = (216,[0]),
      wBound_ = (216,[1024]), bufferSize_ = 1024, and my Bool reading of TMemBufCtorInv (live heap u8 array, offsets within it) is
      true in both old units: the shape TMemBufCtorInv asks for. n = 1024 is in initCommon_establishes'
      range; n ≥ 2 is needed because a 1-byte malloc gets the scalar type u8 at its first cast (Eval.lean l.986-995).
  (d) shared_ptr<TMemoryBuffer>(TMemoryBuffer*), run in place on the RequestContext's obuf field (G4), allocates a heap block of
      type _Sp_counted_ptr<TMemoryBuffer *, _S_atomic> (counts 1/1) and sets obuf._M_pi = (block,[0]). CtorInv admits it
      (SpBasePtrInv's second branch; my Bool reading true, no closure violation), and complete is then UB in both versions of both
      pairs, "type-punned access (byte-level access not modelled)" (G4a-C; G5 = program-made TMemoryBuffer + program-made control
      block; MC = hand-made control block). With the control-block pointer set to null by hand the same states return in both
      versions (G4a-N, G5-N). RequestContext's only constructor initialises ibuf and obuf through shared_ptr(T*), so no
      constructor in the units leaves an _M_pi null.
  (e) MbufFreeClosed constrains every block of the memory: a block of an MbufFree type (outside both lists) that points to a
      TMemoryBuffer, a byte array, a control block, a RequestContext or a stack block violates it. In the running server complete
      is called through the std::function made in process from std::bind(&TEvhttpServer::complete, this, ctx, _1); the bound
      object (record std::_Bind<...>, 072-old Gen l.503) holds the RequestContext pointer, so if it occupies a block of its own
      type that state is outside CtorInv. Not evaluated (the call goes through the processor, outside these units).

## 4. Axioms: PASS (probe_P_ax.out, probe_P_walk.out, verdict_axioms.tsv, axset_counts.tsv)
- In Lean 4.35 #print axioms (collectAxioms) does not walk imported bodies: it reads the axiom records each .olean stored when
  it was compiled (exportedAxiomsExt, toolchain src Lean/Util/CollectAxioms.lean). Hence two runs, both in fresh processes:
  - records: collectAxioms of every theorem constant of the 29 package modules (2722, enumerated from the module data, auxiliary
    ones included) and #print axioms of the source-declared theorems (658 of 661 printed; see Deviations): all within {propext,
    Classical.choice, Quot.sound} (544 all three, 767 [propext, Quot.sound], 1029 [propext], 2 [Classical.choice], 1
    [Quot.sound], 379 none). equivalent, changed_only_where_old_unsafe, nonvacuous, witnessMem_ctorInv, complete_eq_of_ctorInv
    and the five lemmas, in both modules, print exactly [propext, Classical.choice, Quot.sound]; WT_iff [propext].
  - walk: my DFS from the 2722 theorems over the constants used in types and values (definitions, theorems, opaques, inductive /
    constructor links, recursor rules), marking at push, no records: 12977 constants visited, 0 missing; axioms reached:
    propext, Classical.choice, Quot.sound. The imported environment declares 12 axioms in all (propext, Classical.choice,
    Quot.sound, sorryAx, Quot.lcInv and the compiler's lcAny, lcCast, lcErased, lcProof, lcUnreachable, lcVoid, isScalarObj).
- Planted controls in the same processes: a sorry theorem gives [sorryAx], a theorem from a declared axiom [ctl_ax], a
  native_decide theorem its auxiliary axiom ctl_nd._native.native_decide.ax_1_1, Classical.em the three; walk and records agree
  on all of them.

## 5. Kernel replay: PASS (lc_summary.tsv, lc/, lcctl_v2/; scripts/lcone.sh, scripts/lcctl_v2.sh)
- leanchecker in my copy, LEAN_PATH = copy lib + frozen c17690c build (as the template), LEAN_NUM_THREADS=1, PATH = toolchain
  bin. Plain mode (the module's own declarations against its imports) for each of the 29 package modules: 29/29 rc 0, no output
  (O072 96.5 s, O105 104.2 s, the others at most 28.6 s). --fresh VOEquiv.CheckAll2 (the closure of both verdict modules from an
  empty environment): rc 0, 318.2 s (producer's log: 308 s).
- Planted controls: a module whose olean holds lcCtlBogus : False := True.intro, added with debug.skipKernelTC (its own
  #print axioms says "does not depend on any axioms"): rejected, rc 1, "(kernel) declaration type mismatch"; a valid module rc 0;
  a missing module rc 1.

## 6. Gen: PASS (gen_cmp.txt, files_vs_tier1.tsv, diff_vs_tier1/; scripts/cmp_tier1.sh)
- The 4 Gen modules (072: d10129d4 / c98e79ad, 105: 9c7c8e6e / 7a3e7bd1) are byte-identical to the tier-1 package's, Unit.lean
  and Unit.olean (8/8 cmp). The tier-1 check's regeneration (cir2lean of the frozen build on the T3 unit.cir, identical except
  line 2) therefore holds for them, and there is no difference to classify.
- Whole package against the tier-1 package by path: 57 SAME, 8 DIFFERENT (REPORT.md, leanchecker_replay.log, Congr.lean/.olean,
  O072 and O105 .lean/.olean), 12 NEW (CompleteCtorCongr, GetBufferEval, MbufFreeModels, TMemBufOps, UptrEval, CheckAll2, each
  .lean + .olean). Congr.lean differs by one added block after l.3279 (224 lines: noDiffTy, recordClosedUnderNoDiff, record? and
  sizeAlign lemmas) and nothing else, so mkCompleteWitnessMem is the tier-1 one.

## 7. The witness (probe_P_wit.out; probe/P_wit.lean)
- witnessMem = mkCompleteWitnessMem <old unit module> (Congr.lean l.3269): RequestContext 83 -> request 84 (evhttp_request, no
  connection), empty evkeyvalq lists 85/86, obuf._M_ptr -> TMemoryBuffer 87 with rBase_ = rBound_ = wBase_ = wBound_ = (88,[0]),
  88 a heap u8[1] holding [0]; ibuf._M_ptr, ibuf._M_pi and obuf._M_pi all null. Args [this = null, ctx = (83,[]), true].
- CtorInv: witnessMem_ctorInv (kernel-checked in the fresh replay; axioms the three) and my Bool reading of CtorInv (true in
  both modules). The Bool reading computes each conjunct from the memory; it is evidence, not a proof.
- evalCallIter (100000 steps) of complete, old and new, success true and false, 072 and 105: ok, ret in 8/8; blocks 83-86 are
  freed, 87/88 stay live (the null control block owns nothing).
- Reached: with the output-header list 86 retyped evkeyval the run is UB in evhttp_add_header ("the list is not a live struct
  evkeyvalq"); with the request block on the stack it is UB in evhttp_send_reply ("not a live heap struct evhttp_request of
  libevent 2.1's layout", old and new). With wBase_ = (88,[1]) (a 1-byte body, still in CtorInv) both versions return. Not
  exercised by the witness: a non-empty body (sz = 0), a control block, the release of obuf, the error branches.
- Shape: the witness's TMemoryBuffer value has seven members (base, u8[7], buffer_, bufferSize_, maxBufferSize_, owner_, u8[7]:
  the 072-new layout) in all four units, while the old units' record has six (buffer_ at member 1); CtorInv permits this and
  complete reads only rBase_/wBase_. Block 88's type u8[1] is not one the allocator produces (see 3(c)).
- The tier-1 counterexample memories (rebuilt from the tier-1 sources): my Bool reading gives TMemBufCtorInv false for both; in
  these terms old returns and new is UB at evbuffer_add ("the data is not a char range"), as in tier-1.

## 8. The _M_pi note (probe_P_uptr.out; probe/P_uptr.lean)
- evalCall_M_release_ub (UptrEval.lean l.915-981; #check in a fresh process): for every ctx with HasUptrCtx, every m and
  b_sp < m.next, if for every m' that agrees with m on block b_sp the 64-bit typed load at (b_sp, path ++ [1]) is .ub
  "type-punned access (byte-level access not modelled)", then _M_release on (b_sp, path) returns exactly that UB. The hypothesis
  is the punned load itself; spPtrValid_of_spBasePtrInv discharges it under HasCompleteCtx (ta_sp_counts: member [0,1] of
  _Sp_counted_ptr<TMemoryBuffer *, _S_atomic> is s32) for every live heap block of that type at path [0]. My composition of the
  two type-checks (U1), and HasCompleteCtx is proved for all four units (U2).
- evalCall_uptr_dtor / uptrDtorRes: complete's final unique_ptr<RequestContext> destructor returns .ok only when both _M_pi are
  null, and the same UB otherwise (under SpPtrValid of both).
- So REPORT section 2's sentence ("every related .ok execution of complete has _M_pi = .null") follows within CtorInv from these
  lemmas; the package states it in prose, not as one theorem. Outside CtorInv a control block of an undeclared record type passes
  the load (checks/t1expo-20261029T172130Z); SpBasePtrInv excludes such blocks. The evaluations agree: live _Sp_counted_ptr
  control blocks give that UB in both versions (MC, G4a-C, G5), null ones return (witness, G4a-N, G5-N).

## Verdict
- equivalent, changed_only_where_old_unsafe and nonvacuous for 072 and 105 are proved and kernel-checked as stated: the T3
  obligation plus the bool, with the added hypothesis CtorInv x1 m. They are consistent with the tier-1 refutations, whose
  counterexample memories violate CtorInv.
- What they cover: on the CtorInv domain the two versions of complete give equal outcomes. Inside that domain, states with
  program-made control blocks make complete UB in both versions, so the theorems relate UB to UB there; the .ok executions they
  relate all have null control blocks, which no constructor in the units creates, and the program's own RequestContext
  constructor is UB in these terms. The TMemBufOps lemmas show, for the old units, that initCommon (and, by evaluation, the
  TMemoryBuffer constructor) puts obuf's two pointers in the CtorInv shape, and nothing more of CtorInv.
- So the theorems do not establish agreement of the versions on a state the program creates; they bound the tier-1 difference
  to memories outside CtorInv.

## Deviations and limits
- Bare-shell reads beyond one file: one recursive listing (ls -laR) of the package at the start, one recursive grep -rn over the
  package's src/ for definition sites, one cat of the five small lcctl v1 output files. All read-only.
- Bare awk commands that wrote new files of mine: probe/P_t072new_v2.lean and scripts/lcctl_v2.sh (each from my v1 file), and a
  first verdict_axioms.tsv (malformed; rewritten by scripts/postproc.py in a guarded job).
- Probe defects, rerun: gen_probes.py's text comparison over-captured the package's equivalent (term-mode proof; the regex ran to
  the next ":= by"), so stmt_compare.txt says False for equivalent; superseded by stmt_compare_v2.txt (True for both). In P_ax,
  3 of the 661 source "#print axioms" lines used names my parser built wrongly (theorems declared _root_.EquivLean.Cir.* inside
  Tactic.lean's namespace): "Unknown constant", rc 1; the 3 theorems are in the records enumeration (standard axioms).
  P_t072new.lean hit the default maxRecDepth in its rfl checks; P_t072new_v2.lean sets 100000 as the package does. lcctl.sh (v1)
  lacked the toolchain bin on PATH (leanchecker found elan's shim: "no default toolchain", rc 1 for all three controls):
  invalid, superseded by lcctl_v2.
- Not done: recompiling the package sources (the probes elaborate my statements against the package .olean files; the
  records-free walk covers the axiom question for the stored terms); evaluating the server's path through the processor;
  re-running cirlean's case files; G2 in the two new units.
- Jobs: every lean, leanchecker and interpreter run and every multi-file scan ran as one job under pjobs_v3 + coreh_guard_v2 with
  ulimit -v 32 GiB; at most 8 at once (the batches did not overlap). Core-h: 0.173 over 49 guard logs (coreh.txt); the coreh and
  SHA256SUMS jobs come after that count.

## Files
scripts/ (sums_copy.sh, mk_lc_cmds.sh, lcone.sh, collect.sh, gen_probes.py, probe1.sh, lcctl.sh, lcctl_v2.sh, cmp_tier1.sh,
postproc.py, coreh.sh, make_sums.sh); cmds_*.txt, pjobs_*.log/.out, guard/; sums_before.txt, sums_after.txt, *_sums_abs_*.txt,
*_check_*.txt; lc/, lc_summary.tsv, pkg_modules.txt; probe_P_*.out; stmt_compare.txt (v1), stmt_compare_v2.txt;
verdict_axioms.tsv, axset_counts.tsv; files_vs_tier1.tsv, gen_cmp.txt, diff_vs_tier1/; lcctl/ (v1, invalid), lcctl_v2/;
probe_src/ (copies of the probe files and control modules); coreh.txt; SHA256SUMS (scripts/make_sums.sh; that job's guard
and pjobs logs are in the replay dir, guard_final/, so that no file here changes after hashing).
