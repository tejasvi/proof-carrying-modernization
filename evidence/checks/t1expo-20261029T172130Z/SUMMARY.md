RESULT: The 24 tier-1 closures (complete: 37 functions + 13 reached only by virtual calls, in each of 22 units; breakLoop: 8 functions, 2 units) hold sites of 5 of the 12 kinds plus the shared_ptr counter read: K1 (getBuffer ptr_diff; notify byte stride), K8 (26 model calls per complete unit, 3 in breakLoop), K10/K11 (std::thread::id: trivially copyable, no pointer), K12 (__libc_single_threaded load; std::cerr and GlobalOutput addresses), K13 (_M_release's 64-bit read of the two 32-bit counters, 22 units); K2-K7 and K9 have none. At c17690c (27 commits after 424e821) K1 and K4 are fixed, K5 and K8 partly fixed, K2, K3, K6, K7 and K9-K12 open, and K13 is UB (code, cirlean's own case files run at c17690c, and the earlier probes re-run on 424e821 and c17690c). On executions the theorems relate, no site lets the semantics depart from C in the way its kind describes. The K13 read is UB for every control block of the declared class (evaluated in all 22 units), so the 11 complete verdicts relate only executions whose RequestContext has null control blocks or control blocks of a type the unit does not declare (such an execution passes the read and returns), and the K12 load lies behind it. notify's stride and the breakLoop(true) reads are unreachable (poll, TOutput::printf/instance: no body, no model). The witnesses pass the getBuffer ptr_diff (equal sizes), 6 model calls (complete), 2 model calls and the thread::id sites (breakLoop); neither passes the K13 read or a K12 read. Q4: at c17690c a declared-only global still reads as zeros (cirrun 1, 1 vs native 42, 31); the statements quantify over all memories, and the complete witness (built on Module.initMem) reads none.

# Check by an agent: exposure of the cirlean C-semantics defects in the tier-1 re-proof (12 Thrift T3 verdicts, extmodels c17690c)
Written 2026-10-29T18:21:02Z (date -u). Dir: this directory. Inputs read only: package copy ~/fv_paper/replay/tier1-20261029T164912Z/pkg (sha256sum -c 131/131 OK, pkg_check.txt), frozen worktrees ~/cirlean_frozen/extmodels_c17690c_20261028 and next2_424e821_20261027 (cited files and binaries hashed in cited_sha256.txt, kinds/inputs_sha256.txt), cirlean git history (local, GIT_ALLOW_PROTOCOL=file), T3 unit.cir inputs ~/fv_paper/replay/t3-20261026T2147Z/runs. The T3-era screens describe ffab71e only; every site below comes from the tier-1 terms.

Kinds (brief order): K1 pointer arithmetic/difference whose pointee size differs from the element size of the object
reached; K2 scalar store at the address of a whole aggregate; K3 aggregate copy through another record type; K4 strtol
end pointer; K5 va_arg or scanf type mismatch; K6 union member pointer kept and used later; K7 bit-field read through a
union member; K8 library call whose argument types, NULL or size-0 arguments the models treat differently from C; K9
store through const; K10 by-value parameter of a non-trivial class; K11 record returned by value holding a pointer into
itself; K12 read of a global the unit only declares; K13 (lead's item) libstdc++'s read of the two 32-bit shared_ptr
reference counters as one 64-bit word.

## Status of each kind at c17690c
c17690c descends from next2 424e821 through 27 commits of the next3 line (git -C ~/cirlean log --oneline
424e821..c17690c; no remote, no promisor pack). Evidence per kind: (i) the commit that changes it, (ii) the code at
c17690c, (iii) cirlean's own case files run with the frozen tree's tests/difftest/run.sh at c17690c (LIB=libstdcxx,
DIFF_W in this directory; kinds/own_*.out: bytes 30 MATCH + 8 UB, recpun 16 + 9, modelstore 10 + 9, modelstore2 6 + 11,
vastruct 9 + 6, vafmt 8 + 16, overlap 7 + 6, each as labelled), (iv) the probes of the earlier checks (stride, coresnd,
libsnd, byval, extglob; their CIR files copied, nothing rebuilt) run on both frozen cirrun builds (kinds/results.tsv,
73 cases; native values copied from the original result files).
| kind | status | evidence |
|---|---|---|
| K1 | fixed | fa199c7 ("cir.ptr_stride / cir.ptr_diff count objects of the pointer's type ... which was a soundness bug"): Ctx.stride?/diff? (CIR/Semantics/Basic.lean l.901-938). Own test bytes: 30/30 MATCH incl. the char* and short* strides, struct* strides and char pointer differences. Probes: c_char_stride, c_short_stride, c_char_diff, c_heap_char_stride and the C maintainer session's two cases equal the native values (424e821: 4, 2, 1, 40, and UB at k = 3). Still UB where the native run is defined: c_char_over_struct (a char read of a struct's bytes; byteOf covers scalars only, l.552-560) and c_int_over_struct (UB under the strict subobject reading the maintainer adopts); heap storage typed by its first cast (labelled gap in bytes.cpp). These are reports of UB, not other values. |
| K2 | open | no commit in the range; Mem.punnedAccess and Ctx.punnedMember test only scalar targets (Basic.lean l.218-227, l.492-504), so storeTy writes the scalar over the record (l.246-251). Probes g5_byte_struct/array/nested/heap give 7/8 (native 305419783/4), g5_ll_struct is defined, g5_byte_then_member is UB, as at 424e821. |
| K3 | open | cir.copy is typedLoad + typedStore of the record type (Eval.lean l.607-612) with no check of the record's identity; g4_copy_other 2/3 (defined; C: UB), as at 424e821. |
| K4 | fixed | 28083d1 (library models store into caller memory through Ctx.typedStore). Own test modelstore: the five ub_strto*_end_into_* cases UB, the t_* cases MATCH. Probe g2_strtol_end_into_int: UB "type-punned access" (424e821: 2/3 defined); control c_strtol_end_ok matches. |
| K5 | partly fixed | 4d7aaa3 (va_arg checks the type the argument was passed with), 0bf1704 (va_list life, printf literal formats), 28083d1/2f9ef37 (strict sscanf target types). Own tests vastruct and vafmt as labelled; modelstore's four ub_sscanf_* cases UB. Probes l_va_long_of_int and l_va_after_end UB (424e821: 5 and 12). Open: a call through a function pointer passes values only (vafmt t_gap_va_fnptr: an int read as long gives 5, labelled gap; vastruct t_indirect_struct labelled gap). |
| K6 | open | a union member becomes active when its pointer is formed (Eval.lean l.617-629, unchanged in the range); u1_stale 1000 (native 0), u1_stale_ints 5 (7), as at 424e821. |
| K7 | open | u2_bits_after_float 0 (native 133169152), as at 424e821. |
| K8 | partly fixed | 2a9990b (mem* pointers valid also at length 0, sprintf/snprintf format overlap, fprintf's stream), 0bf1704 (printf-family literal formats against the argument types), 28083d1 (typed stores). Own tests modelstore2 and overlap as labelled. Probes l_memcpy/memset/memcmp_null0, l_sprintf_fmt_overlap, l_sprintf_d_long UB (424e821: the native values). Open: a printf-family call with a non-literal format is not checked (0bf1704). |
| K9 | open | Op.alloca carries no const flag (CIR/Syntax.lean l.203); only constant globals are read-only (CIR/Semantics/Init.lean l.21). l_const_local_store2 gives 2 (the store through the cast is visible; C: UB), as at 424e821. |
| K10 | open | arguments are bound as values (Basic.lean bindArgs l.157); t_move_from_param -1 (native 0), as at 424e821. |
| K11 | open | t_self_ref_return UB "invalid memory read" (native 1), as at 424e821 (a report of UB, no other value). |
| K12 | open | Module.initMem zero-fills globals without initializer (Init.lean l.4-23); t_ext_scalar/t_ext_array 1/1 (native 42/31), as at 424e821; 2a9990b only gives stdin, stdout and stderr distinct non-null handles. |
| K13 | UB (since 424e821) | Ctx.punnedMember (member type s32, access s64); fa199c7 keeps "libstdc++'s 64-bit counter read (wider than a byte)" UB. Own test recpun: r_pun_ll_over_ints, r_pun_atomic_ll_over_ints ("libstdc++ shared_ptr _M_release"), the volatile, atomic-store and fetch_add variants all UB. Tier-1 terms: probe_cb (below). At 424e821 (checks/t23next2-20261028T061053Z, section 4) cirrun gives the same UB in 12/12, e6ac99a returned the use count alone, and the native run returns use + 2^32 * weak. |
| width, member level | fixed | the one-element meaning of a narrower access: fa199c7 makes a char access a byte access (c_byte_member now gives the native 305419783; 424e821 UB) and keeps wider accesses UB. |

## Method
- Terms: the 24 pkg/src/Gen/*/Unit.lean, parsed by scripts/t1lean_v3.py (large functions are split into
  `abbrev ..._opsK : List Op` lists; v3 resolves them). Closures (scripts/scan_t1_v6.py): direct calls from the root;
  a callee with `model := some _` is a leaf (evalCall runs the model, CIR/Semantics/Eval.lean l.1431-1432); a callee
  with neither body nor model is a UB leaf (l.1435). Virtual tier: the targets of each virtual call are the vtable
  functions whose `this` class is the static class or derives from it (adjustThisIndirect, Eval.lean l.362-374;
  arbitrary vptrs in the statements' memories allow any such slot), closed to a fixpoint. Result (closures.tsv,
  closure_funcs.tsv, vcalls.tsv): complete 37 direct + 13 virtual-tier functions (all _Sp_counted_ptr/_Sp_counted_base
  members), models evbuffer_add/free/new, evhttp_add_header, evhttp_send_reply, 3 ostreamOut symbols, operator delete,
  __cxa_pure_virtual, no UB leaf, in each of the 22 units; breakLoop 8 functions, models abort, event_base_loopbreak,
  pthread_self, UB leaves TOutput::printf, poll, send, close, __errno_location (+ TOutput::instance in the new version).
- Screens per kind on every op of these functions (ophist.tsv): stride/diff ops with an intra-procedural pointer trace
  (casts, members, elements, allocas, globals, local slots, callers' arguments); scalar loads/stores and record
  copies/loads/stores traced to aggregates or reached through casts from aggregate/other-record pointers; calls to
  strto*/ato*/scanf names; va ops; unionMember uses; get/setBitfield through a union member; every call to a FuncDecl
  with a model and every cir.libc op, with constant arguments; const allocas (CIR `const` attribute, matched by
  alloca order) with stores beyond the initialization, stores into constant globals; record-typed parameters,
  arguments and returns with the class's special members in the unit; getGlobal of `init := none` globals and their
  uses. Raw rows: scan_v6/sites_raw.tsv (1082 rows incl. 374 init-only const allocas, which are not K9 sites). K13:
  scripts/counter_sites.py (counter_sites.tsv: the atomic acquire s64 load of _M_release in every unit).
- CIR location: each op is mapped to the T3 run's unit.cir (the cir2lean input, regenerated byte-identical by the
  tier-1 check) by its ordinal among ops of the same kind in the same function; the counts agree in every function
  holding a site, so every op-level location is exact; source file:line from the op's #loc.
- Semantics read at c17690c: Ctx.stride?/diff? count units of the pointee type (byte view when the element size
  differs; element units only when a size is unknown) (Basic.lean l.901-938); typedLoad/typedStore with
  Ctx.punnedMember for record members (l.484-505, l.628-644); Module.initMem zero-fills globals without initializer
  (Init.lean l.4-23); loads through `.vtable` pointers read the module initializer and are UB for a declared-only
  vtable (Eval.lean l.97-123); library models CIR/Std/Models.lean (libevent l.889-1110, ostreamOut l.1693-1701,
  freeHeap l.613-618). Observation: ObsEq m0 = equal exit and equal blocks below m0.next (pkg
  EquivLean/Bridge/Cir/Obs.lean l.25-26).
- Witness passage and controls (probe/P*.lean from scripts/gen_probes_v2.py; probe/P_cex.lean; probe_cb/P_cb_*.lean
  from scripts/gen_probes_cb_v2.py): an op `.unknown "MARK_k" []` is inserted before the site op (pre-order op index,
  the scanner's order), the verdict's own witness (args and witnessMem of its VOEquiv module), or a variant of it, is
  evaluated with evalCallIter, 10000 steps, as in the tier-1 check; PASSED = the run stops at the marker. 12 + 1 + 11
  probe files, all rc 0. The unmarked witness returns in 24/24 units; markers at function entries give the functions
  entered (FN_ENTRY rows).

## K13 (lead's item): libstdc++'s 64-bit read of the shared_ptr counters
- Site: _M_release's `__atomic_load_n(reinterpret_cast<long long*>(&_M_use_count), __ATOMIC_ACQUIRE)`
  (bits/shared_ptr_base.h:336); in the terms op 30 of _M_release: getMember 1 (s32), bitcast to s64*, `.load` of s64
  (cir2lean keeps no atomic attribute; the CIR op is `cir.load ... atomic(acquire)`), in all 22 complete closures
  (counter_sites.tsv, e.g. 032_c194044c8d0c_cpp/cir/9197ce06/thrift_async_TEvhttpServer/unit.cir:2773). The
  TNonblockingServer units hold _M_release too, but the breakLoop closures do not reach it.
- (a) c17690c treats the load as UB for every control block of the declared class: the member's type s32 is not
  access-compatible with s64 (Ctx.punnedMember). Evidence: recpun's own cases (above) and probe_cb rows "decl 1/1": the
  complete witness memory with obuf given an _Sp_counted_ptr<TMemoryBuffer*> control block, counts 1/1, ends in UB
  "type-punned access" in all 22 units, and the marker before the load is passed (earlier probe/P*.out CB rows: counts
  1/1 and 2/1, the marker before the following __exchange_and_add_dispatch call is not passed).
- (b) Executions related by the 12 theorems that pass the load: only on memory whose control block is a live block whose
  type gives no member type at the counter path. probe_cb rows "undecl 1/1" and "undecl 2/1": a heap block of a record
  type the unit does not declare, shaped like _Sp_counted_ptr<TConfiguration*> (its vptr, counts 1/1 resp. 2/1, owned
  pointer null): complete passes the load (marker) and returns in both versions in all 22 units, through dispose and
  destroy for 1/1. With a declared record whose member 1 is 64 bits (anon_struct.0 {s64, s64}, the same in all 22
  units) the load passes and a later 32-bit counter access is UB (rows "s64 member"). A release with a live control
  block of the class libstdc++ creates (_Sp_counted_ptr, _Sp_counted_ptr_inplace, all _Sp_counted_base objects) is UB,
  so no execution from a constructed state passes the load, and RequestContext's constructor (operator new, the
  TMemoryBuffer constructor, shared_ptr<TMemoryBuffer>(T*) for ibuf and obuf) always creates such control blocks, which
  ~RequestContext releases on every exit of complete. The 11 complete verdicts (9 proved; 072 and 105 refuted) thus
  relate only executions with null control blocks, as the witness has, or with control blocks of an undeclared type.
  The breakLoop verdict relates no execution through it.
- (c) Neither witness passes it: complete's witness has null control blocks and enters no _M_release (FN_ENTRY rows,
  22 units); breakLoop's closure has no release.
- Further on that path, a virtual call on a TMemoryBuffer object (_M_dispose: delete) is UB in these units: the
  TMemoryBuffer vtable is declared only (init := none) and Ctx.vtableSlot? gives no slot.

## Q1: sites in the tier-1 terms (sites.tsv: 745 rows = 730 site rows + 15 rows "no site"; class column A-S)
| kind | sites (function, source) | units | class |
|---|---|---|---|
| K1 | TMemoryBuffer::getBuffer, ptr_diff wBase_ - rBase_ (u8*, both loaded from members); TBufferTransports.h:586/590/591/618/619 by version | 22 | A |
| K1 | TNonblockingIOThread::notify, ptr_stride pos += ret (char* over the local pointer conn); TNonblockingServer.cpp:1337 | 2 | L |
| K8 | complete: evhttp_add_header (TEvhttpServer.cpp:127/134), evbuffer_new (:133/140), evbuffer_add (:141/148), evhttp_send_reply (:148/155), evbuffer_free (:150/157) | 22 | B-F |
| K8 | complete: 17 ostreamOut calls on the three error branches (cerr << ..., :130/136/144 by version) | 22 | G |
| K8 | operator delete in default_delete<RequestContext> (unique_ptr.h:85) | 22 | I |
| K8 | virtual tier: operator delete in _Sp_counted_ptr<TConfiguration*>::_M_dispose, its D0 and _Sp_counted_ptr<TMemoryBuffer*> D0 (shared_ptr_base.h:418/425) | 22 | K |
| K8 | breakLoop: pthread_self (in this_thread::get_id, std_thread.h:366), event_base_loopbreak (TNonblockingServer.cpp:1437), abort (:1426) | 2 | M, N, O |
| K10 | std::thread::id by value: breakLoop -> Thread::is_current (TNonblockingServer.cpp:1433), is_current -> operator== (Thread.h:80); parameters of is_current, operator== | 2 | Q |
| K11 | this_thread::get_id returns std::thread::id (call in is_current, Thread.h:80) | 2 | R |
| K12 | __gnu_cxx::__is_single_threaded: load of __libc_single_threaded (sys/single_threaded.h:29) | 22 | J |
| K12 | complete: getGlobal std::cerr on each error branch (iostream:66), passed to ostreamOut only | 22 (3 each) | H |
| K12 | breakLoop(true): getGlobal apache::thrift::GlobalOutput (TOutput.h:56), passed to TOutput::printf only | 2 | P |
| K13 | _Sp_counted_base::_M_release, the 64-bit counter read (shared_ptr_base.h:336) | 22 | S |
| K2, K3, K4, K5, K6, K7, K9 | none | 24 | NONE |
| K13 | none in the breakLoop closures | 2 | NONE |
- Absences (ophist.tsv, sites_raw.tsv): the complete closures hold no copy, unionMember, get/setBitfield, vaArg or
  cir.libc op and no strto*/scanf call; their 108 scalar stores and 140 scalar loads have no address traced to an
  aggregate or reached through a cast from an aggregate pointer; their 17 const allocas are stored once, at their
  initialization. The breakLoop closures hold 2 record copies of std::thread::id (same type), no union, bit-field,
  va or libc op, no const alloca. std::string functions are all models in these terms, so the std::string union (whose
  layout the tier-1 front end changed) is not accessed.
- K10/K11 are listed because the operations occur; std::thread::id has no copy or move constructor and no destructor in
  the unit and holds one integer, so neither is an instance of the by-value or self-pointer defect.

## Q2: reachability in related executions and effect on outcomes (per class; full reasons in sites.tsv)
"Related" = both versions Safe on a WT memory. The statements bound only block ids, so reachability is stated with the
memory it needs; for the 10 proved verdicts the two versions evaluate equally for every input (complete_eq;
breakLoop_false_eq, and breakLoop(true) is UB in both versions), so no site can make them differ.
- A getBuffer ptr_diff: reached by every related execution of complete (evbuffer_new never returns NULL in the model).
  No departure from C: c17690c divides the byte difference by the pointee size when the element size differs (K1
  fixed); on the witness and on constructor-made buffers both operands lie in one u8 array (equal sizes, not an
  instance). In 105's counterexample memory the operands lie in an array of vtable records of 160 (old) or 168 (new)
  bytes and the result is the byte difference (0 old, -8 new), the C value for those addresses.
- B-F, I (evhttp_add_header, evbuffer_new, evbuffer_add, evhttp_send_reply, evbuffer_free, operator delete): reached by
  every related execution of complete. No argument handling other than libevent 2.1.12's: literal key/value without
  CR/LF; evbuffer_add with size 0 and a valid pointer returns 0 (a NULL pointer with size 0 is UB in the model and in
  C11 7.1.4p1); send_reply without a connection frees the request as libevent does; NULL checks as in C. Model
  assumptions outside the 12 kinds (trust base, as in the tier-1 check): allocations succeed, thread id 1, a request with
  a connection counts as freed at once, EVHTTP_REQ_DEFER_FREE and non-char data are UB (coverage only).
- G, H (error branches): reachable only on memories whose string-literal blocks of the header key/value hold CR or LF
  (evbuffer_new never NULL; evbuffer_add returns -1 only on size_t overflow); not on Module.initMem. std::cerr is only
  checked for liveness by ostreamOut, not loaded; the model writes no output and leaves the stream object unchanged
  where C++ resets its width (a model abstraction outside the 12 kinds), equally in both versions.
- J, K (__libc_single_threaded; virtual-tier deletes): only after the K13 read, i.e. only on memories whose control
  block is not of the declared class; the witness does not reach them. The K12 load reads whatever the memory holds:
  the statements quantify over every memory, so the zero fill of Module.initMem does not enter them.
- S (K13 read): see the K13 section: passed only with control blocks of an undeclared type; UB for every control block
  of the declared class, so executions with such a control block are not related (a bound on what the theorems cover).
- L (notify stride), O (abort), P (GlobalOutput): unreachable in any related execution: poll, TOutput::printf and
  TOutput::instance have neither body nor model.
- M, N (pthread_self, event_base_loopbreak): reached when threadId_ = 1; NULL base gives -1 as libevent, a live base 0;
  the return value is unused.
- Q, R (std::thread::id): reached by breakLoop(false); bitwise copies are the C++ copies of this trivially copyable
  class, which holds no pointer.
- 072 and 105 (refuted): the counterexample executions (probe/P_cex.out) pass A and D in both versions; the new version
  is UB at D because the data is not a char range under the new layout, and in 105 the operands of A differ by the
  vtable-record size. Both memories come from no constructor in the closures (tier-1 check); on constructor-made states
  complete is UB in both versions (K13).

## Q3: sites passed by the nonvacuous witnesses (probe/P*.out)
- complete (each of the 11 verdicts, old and new unit; args [null, block 83, true], mkCompleteWitnessMem): passes A
  (both operands (88,[0]) in a u8[1] block: equal sizes, result 0), B, C, D (sz = 0 with a valid pointer), E (no
  connection: the request is freed), F and I. It passes no G, H, J, K or S site and enters neither _M_release nor any
  virtual-tier function.
- breakLoop (args [block 0, false], threadId_ = 1, eventBase_ = NULL): passes M, N (NULL: -1), Q and R; not L, O or P.
- So neither witness passes an instance of the kinds: the K1 site with equal sizes, the K8 calls with arguments treated
  as in C, the K10/K11 sites with a trivially copyable class without pointers, no K12 read and no K13 read.

## Q4: declared-only globals at c17690c
- Run (scripts/q4_extglob.sh, guarded): the frozen c17690c cirrun (nothing rebuilt) on the extglob probe's use.cir
  (copied to q4/; hashes in q4/inputs_sha256.txt; use.c equal to the extglob SHA256SUMS entry): t_ext_scalar 1,
  t_ext_array 1, t_defined 8 with k = 1 (q4/results.txt); native (def.c linked, extglob results.txt) 42, 31, 8; 424e821
  gives the same (kinds/results.tsv). So a global that the unit only declares still reads as zeros (Init.lean l.4-23).
- In these verdicts the zero fill enters only executions that start from Module.initMem: the complete witness
  (mkCompleteWitnessMem builds on it), which reads no declared-only global (Q3), and cirrun. The breakLoop witness
  memory holds no global block. The statements quantify over all memories.

## Deviations and limits
- Static screens: pointers loaded from memory are not traced (K2/K3 are decided for addresses the program forms);
  indirect calls other than virtual ones do not occur in these closures (vcalls.tsv: all 8 indirect call sites per
  complete unit are virtual); the virtual tier assumes adjustThisIndirect's class check.
- The status column rests on the probes and case files named there; kinds without a probe or case (e.g. K7 with other
  bit-field layouts) are judged from one case and the unchanged code.
- Rule deviations: several read-only multi-file awk/grep reads ran bare (probe outputs, guard logs, one recursive grep
  for evalCallIter over the frozen CIR/ and the package's EquivLean/VerifOrch sources); the command files
  cmds_probes.txt and cmds_probes_cb.txt were written by bare printf loops; one early command did a cd into scripts/
  with output discarded. cirlean's own run.sh ran from the frozen tree with DIFF_W in this directory (it writes only
  there). No file outside this directory was written except the progress file the user's checkpoint rule names.
- Superseded outputs kept (no rm): scan_v2 (stopped on the split op lists), scan_v3, scan_v5 (same sites as scan_v6),
  scratch/test1, scratch/sites_v1_superseded.tsv and sites_v2_superseded.tsv (before the wording fix and the K13
  rows), scratch/SUMMARY_draft1_superseded.md and SUMMARY_v2_superseded.md, scratch/make_table_v3_stage1.py,
  scratch/lib_body_partial_extract_unused.txt, scratch/SHA256SUMS_v1_superseded, probe/P032_cp_try1.out and
  probe_cb/P_cb_032_try1.out (same rows as the final runs).
- Core-h: coreh.txt (the guard logs of this check).

## Files
sites.tsv; counter_sites.tsv; kinds/ (results.tsv, own_*.out, difftest/, inputs_sha256.txt); scan_v6/
(sites_raw.tsv, closures.tsv, closure_funcs.tsv, vcalls.tsv, ophist.tsv); probe/ (P*.lean, P*.out, P_cex.lean/.out,
INDEX.tsv); probe_cb/ (P_cb_*.lean/.out); q4/; scripts/ (t1lean*.py, scan_t1*.py, gen_probes*.py, make_table*.py,
counter_sites.py, run_probe.sh, q4_extglob.sh, kinds_c17690c.sh, run_own_tests.sh, final_checks.sh, make_sums.sh);
cmds_*.txt; logs/; guard/; pkg_check.txt, pkg_sums_abs.txt, cited_sha256.txt, coreh.txt; SHA256SUMS.
