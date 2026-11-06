RESULT: (1) PASS hashes; (2) PASS statements: arity 3/3 and 2/2 in both versions, equivalent / changed_only_where_old_unsafe (negated for 072, 105) have the type of the T3 statement plus the bool (Lean examples type-check in fresh processes), WT = T3 WT plus the bool, nonvacuous as stated; (3) Gen = extmodels c17690c cir2lean output on the T3 unit.cir (24/24 byte-identical except line 2); besides the model attachments the terms differ from T3 in 4 front-end classes (typeinfo records, std::string union layout, rethrow as .resume, atomic cmpxchg); (4) 9 models attached (6 libevent buffer/HTTP, event_base_loopbreak, pthread_self, __cxa_pure_virtual as UB); (5) PASS: 36 verdict theorems print exactly propext, Classical.choice, Quot.sound; planted controls fire; leanchecker --fresh of each of the 12 closures in my copy rc 0; (6) witnesses reach evhttp_add_header and evhttp_send_reply (complete) and event_base_loopbreak with a null base (breakLoop), not only early returns; (7) the 2 refutations are kernel-checked statements about the WT domain whose counterexample memories no constructor in the closures produces.

# An agent (fork of the evidence-owner session): check of veriforch's post-freeze exploratory package t3_extmodels_c17690c (outside the pre-registration)
Written 2026-10-29T17:05:44Z (date -u). Check dir: this directory. Copy: ~/fv_paper/replay/tier1-20261029T164912Z (pkg/ = cp -rL of the package, probe/, regen/).
Package: ~/veriforch/runs/postfreeze/t3_extmodels_c17690c. cirlean: frozen worktree ~/cirlean_frozen/extmodels_c17690c_20261028.

## 1. Package and copy: PASS
- SHA256SUMS sha256 3ab57abc5bbfdfc085e7d2244fd6bddbd1c81de9a17d902f7babc8f281e74194 = announced; REPORT.md f3785471...,
  leanchecker_replay.log b52f0789... = announced (all three computed with sha256sum).
- sha256sum -c: 131/131 OK before (16:49:33Z, recorded in the progress log; no file kept), in the copy (sums_copy.txt; cp -rL,
  0 symlinks) and after all runs (sums_after.txt). Nothing was written in the package or in the frozen cirlean copy.
- REPORT.md lists no .olean hashes. voequiv_olean_sha256.tsv has the sha256 of the 13 VOEquiv .olean files (identical in the
  package and the copy) for comparison with the hashes in the producer's message.

## 2. Statements: PASS (stmt_compare.txt, probe_T1_*.out, probe_AxCtl.out; scripts/stmt_compare.py, scripts/gen_probe.py)
- Arity: every evalCall in equivalent / not_equivalent passes as many arguments as the root FuncDecl has parameters, in both
  versions: complete 3/3 (this, ctx, bool x2) in 22 units, breakLoop 2/2 (this, bool x1) in 2 units.
- Text: after removing the Bool binder and the .bool argument, equivalent and changed_only_where_old_unsafe have the same text as
  the original T3 statements (~/fv_paper/replay/t3-20261026T2147Z/runs/<order>_*/lean_cert/VOEquiv) for the 10 proved verdicts;
  WT is the T3 WT plus the bool for all 12.
- Fresh lean processes (one per module, LEAN_PATH = copy lib + frozen c17690c build): #check of each verdict statement and #print WT;
  'example' checks that type-check against the package theorems: for the 10, the T3 statement with (x2 : Bool) / (x1 : Bool) added
  := equivalent, and EquivOn (Bad <T3 WT + bool> ...) := changed_only_where_old_unsafe; for 072 and 105, the negations of the same
  two statements := not_equivalent, not_changed_only_where_old_unsafe; WT = <T3 WT + bool> := rfl. 0 errors in all 12.
  Negative controls (probe_AxCtl.out): the T3 statement without the bool, and the T3 WT without the bool, both fail (type mismatch).
- nonvacuous (all 12): ∃ args m, WT args m ∧ Safe (evalCall ctx_new ...) ∧ Safe (evalCall ctx_old ...). The T3 files had no
  nonvacuous theorem.

## 3. Program terms (regen.tsv, gen_vs_t3/*.diff, regen_vs_pkg/*.diff, gen_diff_classes.tsv; scripts/regen_ext.sh)
- cir2lean of the frozen c17690c build, run on the T3 run's unit.cir inputs, gives the 24 package Gen modules byte for byte
  except line 2 (24/24).
- Every changed line against the T3 terms falls in one of these classes (gen_diff_classes.tsv, 0 unclassified lines):
  - model attachments: 7 per TEvhttpServer unit, 3 per TNonblockingServer unit (section 4);
  - typeinfo globals: init .other "#cir.typeinfo<...>" becomes .record [.globalAddr ...] (14 per TEvhttpServer unit, 25 per
    TNonblockingServer unit);
  - std::string's union: [uint8[8]] becomes [int8[16], uint64] with padding [uint8[8]] (all 24 units; the same change an agent
    saw at next2);
  - 'throw;' inside a catch handler: .throw none .void none becomes .resume <handler token> (CIR/Frontend/Parser.lean, "cir.throw"
    without operand): 2 sites per TEvhttpServer unit (catch handlers of two std::__shared_count constructors), 7 per
    TNonblockingServer unit;
  - cir.atomic.cmpxchg: .unknown becomes .atomicCmpXchg (1 site per TNonblockingServer unit).
- So the theorems are about the c17690c translation of the T3 CIR, not about the T3 terms plus models alone.

## 4. Models in these closures and their assumptions (models.txt, frozen_check.txt)
- Frozen copy: git worktree at c17690c99039b2621955ad1b3296e3b6b24798d9, no tracked changes; README.md, CIR/Model.lean,
  CIR/Std/Models.lean, CIR/Frontend/Recognize.lean, CIR/Frontend/Parser.lean, CIR/Semantics/Eval.lean = the commit's blobs.
- Attached (model := none in the T3 terms), recognised by demangled name and CIR signature (Recognize.lean):
  - evbuffer_new: a fresh heap libevent.evbuffer block holding no bytes; allocation succeeds (World.current.alloc = true).
  - evbuffer_free: frees a live evbuffer; anything else is UB.
  - evbuffer_add(buf, data, n): appends the n bytes at data, read as a char range; data must be valid also for n = 0; -1 if the
    length would overflow size_t; allocation succeeds; a data range that is not a char range is UB ("byte-level access not modelled").
  - evbuffer_get_length: number of bytes of a live evbuffer; else UB.
  - evhttp_add_header(headers, key, value): -1 if key or value holds CR or LF; else a heap struct evkeyval with heap copies of
    both strings is appended to the evkeyvalq by typed stores, result 0; allocation succeeds; a list that is not a live evkeyvalq is UB.
  - evhttp_send_reply(req, code, reason, buf): req must be a live heap struct evhttp_request of libevent 2.1's layout, else UB;
    the previous response line is freed; without a connection the request (and what it owns) is freed at once; with one, buf's
    bytes move to the request's output buffer and the request counts as freed; EVHTTP_REQ_DEFER_FREE is UB (not modelled).
  - event_base_loopbreak: -1 for a null base, 0 for a live event_base, else UB; the loop itself is not modelled.
  - pthread_self: 1 (one thread, id 1).
  - __cxa_pure_virtual: UB ("pure virtual call"); adds no assumption.
- 22 TEvhttpServer units get the six libevent buffer/HTTP models + __cxa_pure_virtual; the 2 TNonblockingServer units get
  event_base_loopbreak, pthread_self + __cxa_pure_virtual. pthread_equal has a model at c17690c but no FuncDecl in these units.
- Trusted in addition to T3: the environment World.current (allocation succeeds, thread id 1) and the models above as
  descriptions of libevent 2.1.12 / POSIX threads (README: checked against libevent's static library in libev_cases.txt,
  pthr_cases.txt; not re-run here).

## 5. Axioms and kernel replay: PASS (verdict_axioms.tsv, axioms_raw.txt, fresh/*.tsv, probe_AxCtl.out)
- #print axioms in fresh processes for every theorem in the 12 modules (134 theorems): all within {propext, Classical.choice,
  Quot.sound}; the 36 verdict theorems (10 equivalent, 10 changed_only_where_old_unsafe, 2 not_equivalent,
  2 not_changed_only_where_old_unsafe, 12 nonvacuous) print exactly [propext, Classical.choice, Quot.sound]. No sorryAx, no
  Lean.ofReduceBool (the evaluations use decide +kernel).
- Planted controls in the same setting: a sorry theorem prints [sorryAx], a theorem from a declared axiom prints [ctl_ax].
- leanchecker --fresh of each of the 12 VOEquiv modules (each closure separately), LEAN_PATH = copy lib + frozen c17690c build:
  12/12 rc 0, 145-199 s each (pjobs_fresh.log). CheckAll12.lean only imports the 12 modules; it was not replayed separately.

## 6. Non-vacuity witnesses (probe_Wit.out; probe/Wit.lean)
- complete, all 11: args [this = null, ctx = block 83, true], memory mkCompleteWitnessMem (EquivLean/Bridge/Cir/Congr.lean):
  RequestContext 83 -> evhttp_request 84 (no connection), empty header lists 85/86, obuf -> TMemoryBuffer 87 over a 1-byte heap
  block 88 with no bytes written and a null control block, ibuf null. evalCallIter (10000 steps), old and new: returns; blocks
  83-86 are freed at the end, 87/88 stay. The run passes through evhttp_add_header and evhttp_send_reply: with the output-header
  list retyped (mutation A) it is UB in evhttp_add_header, with the request block not on the heap (mutation B) it is UB in
  evhttp_send_reply. The old version also returns with success = false. Not exercised: a non-empty reply body (sz = 0), the release of obuf (null
  control block), the add_header failure branch. this = null is not read by complete.
- breakLoop: args [this = block 0, error = false], TNonblockingIOThread with threadId_ = 1 (= pthread_self) and eventBase_ = null:
  the run calls event_base_loopbreak(null), which returns -1 (eventBase_ = this instead: UB in event_base_loopbreak). The notify
  path is not exercised (threadId_ = 2: UB on the undefined notification fields of this memory).

## 7. The two refutations (cex_excerpts.txt, probe_Wit.out)
- WT (both): fun args m => ∃ x0 x1 x2, args = [.ptr x0, .ptr x1, .bool x2] ∧ (∀ b p, x0 = Ptr.loc b p → b < m.next) ∧ (∀ b p, x1 = Ptr.loc b p → b < m.next).
  It bounds the block ids of the two pointer arguments and says nothing about the contents of memory.
- 072 cexMem = mkCompleteWitnessMem of the old unit with block 87 replaced: rBase_ = rBound_ = (87, [5, 0]), wBase_ = wBound_ =
  (87, [5, 1]), buffer_ = (88, [0]), bufferSize_ 0. Old layout: member 5 of TMemoryBuffer is its trailing 7-byte .pad array, so
  getBuffer gives 1 byte of padding and evbuffer_add returns. New layout (TBufferBase gains a bool; a 7-byte pad at member 1
  shifts the members): member 5 is owner_ (bool); evbuffer_add is UB "the data is not a char range (byte-level access not
  modelled)". The block's value has the old shape under a record name whose layout differs in ctx_new.
- 105 cexMem: block 89 = heap array of 2 anon_struct.5 (the record type of the TMemoryBuffer / TVirtualTransport / TBufferBase
  vtables: 20 pointers old, 21 new; element values are empty arrays); rBase_ = rBound_ = (89, [1], byte 0), wBase_ = wBound_ =
  (89, [0], byte 160). With 160-byte elements both are the same address (0 bytes, old returns); with 168-byte elements they are
  8 bytes apart in the other order; new is UB at evbuffer_add (same message).
- Can these states come from an execution of the program? In the four units the functions that address rBase_, rBound_, wBase_,
  wBound_ are (rbase_writers.txt): the TBufferBase constructor (null), TMemoryBuffer::initCommon (from buffer_, malloc'd when no
  buffer is passed, as RequestContext's constructor does for obuf with new TMemoryBuffer()), TBufferBase::read, readAll, borrow,
  consume, write (moving them within the current buffer), getBuffer and bufferedReadLength (reads). None derives them from the
  object's own address or from a vtable; the vtables are static globals.
- Verdict: not_equivalent and not_changed_only_where_old_unsafe are proved and kernel-checked as stated, over the WT domain. Their
  counterexample memories are admitted by WT (arbitrary contents, one m read under both versions' layouts); no constructor in the
  closures produces them, and the new-side UB is the not-modelled branch of the evbuffer_add model. They do not establish a
  difference between the versions on states the program creates.

## Deviations and limits
- At 16:55:04-16:55:19Z the 13 short probe jobs (5 s each) overlapped the replay runner's last jobs: up to 16 jobs at once,
  above the 8-job cap, for about 15 s.
- probe_Wit.out ends rc=1 because of one probe line of mine (decide on a Mem equality: no Decidable instance); the breakLoop
  witness memory was read from the source instead. All 20 evaluation lines printed.
- Not done: recompiling the package sources (the checks use the package .olean files; the statement checks elaborate the T3 texts
  against them); re-running cirlean's libevent/pthread case files.
- Core-h: 0.629 (27 guard logs, coreh.txt).

## Files
scripts/ (lcfresh.sh, probe1.sh, stmt_compare.py, gen_probe.py, regen_ext.sh), cmds_*.txt, pjobs_*.log/.out, guard/, fresh/,
probe_*.out, stmt_compare.txt, axioms_raw.txt, verdict_axioms.tsv, regen.tsv, regen_vs_pkg/, gen_vs_t3/, gen_diff_classes.tsv,
models.txt, cex_excerpts.txt, frozen_check.txt, voequiv_olean_sha256.tsv, sums_copy.txt, sums_after.txt, coreh.txt.
