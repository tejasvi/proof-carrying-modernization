# T3 (PREREG_T_v1, Thrift CI verdicts over 150 commits): independent check (an agent; written 2026-10-26T22:09Z by date -u)

RESULT: T3 agrees with veriforch's records on every count I recomputed, with two record points. (1) Census rule: the
summary counts a multi-language commit's overall outcome under each language; by each language's own functions,
order 101's C side is unknown (C: 3 / 0 / 23 instead of 3 / 1 / 22). (2) The equivalent theorems lie in 13 commits,
not 10. All 54 equivalent theorems (and their 54 changed_only_where_old_unsafe companions) use exactly the standard
axioms, and their 13 closures replay with rc 0. All 38 behaviour_changed witnesses reproduce from copies (21 C/C++, 17
Java). Spend reproduces exactly (1,672 calls, $189.77; $164.96 in kept records; cap $300).

## Copies and hashes
- Copy: ~/fv_paper/replay/t3-20261026T2147Z. Small files copied (records/ 150, summary_final.md/.json, t3_results.jsonl,
  pins.json, t3_driver.log, LAUNCH_NOTES.txt, START_DIRS*.txt, start_time*.txt, frozen_path.txt, logs/, guard/, replay/,
  superseded/, targets/, T3.guard.log; 82 MB); lean_cert, lean_eqj, ci dirs and the needed unit.cir files of the 26
  witness/theorem run dirs as hard links (cp -al / ln; no .crash_* dirs, no caches or prepass); 0 symlinks.
- Deps (hard links from ~/veriforch_frozen/T3_final_20261025T173358Z/deps): cirlean-ffab71e and
  equivlean-b171660-cir-ffab71e (both = veriforch's live deps, diff -rq rc 0; HEAD b171660b3fd9; no promisor);
  equivlean-751764f-jimple-0149Z (HEAD 751764f) and JimpleLean-20261025T0149Z (SHA256SUMS e4b550c4 = pins.json,
  sha256sum -c rc 0). The frozen manifest SHA256SUMS 32320da9 (208 files) covers orch/targets/scripts/tools/VerifOrch,
  not deps/.
- Announced hashes 7/7 equal (summary_final.md 6cde86b9, .json c1ff8a4a, t3_results.jsonl 0e9b26b0, pins.json
  3f7809c1, records 072 2038ae2b, 090 dee99e15, 103 d1eb3b92); records = prereg/T/t3_commits.tsv by order and commit
  (150/150). records/ in the copy = the live dir (diff -rq empty at copy time).

## Census (tools/t3_outcomes_mine.py, own code; PREREG_C_v2 rules per language from by_language verdicts)
| language | behaviour change shown | certified eq. | certified cons. | partly certified | unknown | unknown: no changed function | blocked: build | entries |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| C++ | 7 | 0 | 0 | 9 | 44 | 12 | 1 | 73 |
| C | 3 | 0 | 0 | 0 | 23 | 0 | 0 | 26 |
| Java | 6 | 0 | 0 | 0 | 25 | 3 | 0 | 34 |
| Rust | 0 | 0 | 0 | 0 | 17 | 3 | 0 | 20 |
| total (commit once) | 16 | 0 | 0 | 9 | 106 | 18 | 1 | 150 |
- Only difference from summary_final: its C row is 3 / 1 / 22, because it counts a commit's overall outcome under each
  language it touches. Order 101 (C + C++) is partly certified overall (C++: 1 equivalent + 34 unknown), but its C side
  has 22 unknown verdicts and nothing else. Order 32 is C++ only (one file, thrift/async/TEvhttpServer.cpp), so the
  coordinator's "order 32 touches C++ and C" does not hold; the extra C entry is order 101. Multi-language commits: 48
  (C + C++, unknown), 101 (C + C++), 120 (Java + Rust, unknown).
- Record verdicts = union of by_language verdicts for all 150; record outcome = my recomputation for all 150;
  t3_results.jsonl has one row per order except order 33 (two identical rows, unknown; the cf1 re-run).
- Unknown: no changed function (18): orders 8, 15, 22, 23, 37, 38, 39, 46, 56, 66, 67, 68, 69, 117, 132, 133, 140, 148.
  Blocked: build (1): order 2 (C++, TJSONProtocol TU; 96 changed functions).
- Equivalent verdicts: 54 in 13 commits (32, 50, 57, 58, 72, 77, 79, 89, 101, 105, 116, 138, 142), all C++. Four of them
  (50, 58, 72, 77) also have a behaviour_changed verdict, so their outcome is behaviour change shown; the other 9 are the
  9 partly certified commits (all C++ entries). Behaviour_changed: 38 in 16 commits (11, 24, 29, 30, 41, 50, 58, 71, 72,
  77, 111, 115, 118, 119, 129, 143): C 3, C++ 18, Java 17.
- Per-function verdicts: unknown 1,426, behaviour_changed 38, equivalent 54 (C++ 820/18/54, C 103/3/0, Java 138/17/0,
  Rust 365/0/0).

## Unknown reasons (outcomes/unknown_reasons.tsv; keyword classes over each verdict's detail)
- C (103): proof failed, no distinguishing input found 101; heartbeat or time limit 1; unsolved goals 1.
- C++ (820): no distinguishing input found 589; domain not mechanical (parameter type without a domain) 102;
  heartbeat or time limit 91; unsolved goals 35; other 3.
- Java (138): Jimple differs only by Soot's local naming/packing (front-end artefact), not proved 61; unsupported
  parameter types 41; heartbeat bound or time limit 35; other 1.
- Rust (365): not translated (Charon/Aeneas/translation gap) 188; generic function, no inputs generated 149; pair
  package modules do not check 17; test unit (checked by its test theorem) 5; other 6.
- Rust crate types: no record uses the census label "statement not well-formed: crate types in the signature"
  (DEVIATIONS T3 Rust note). The crate-type cases appear as "Unknown identifier" (1), "argument types without generated
  inputs" with crate types (5: errors.ProtocolError/ProtocolErrorKind, transport.socket.TTcpChannel, core.fmt.Formatter)
  and "not translated ... Unknown constant `thrift.*`" (40). The census grouping is the evidence owner's.
- Model calls: 204 of the 1,672 calls ended with stop = refusal (witness proposals; e.g. 62 in 072's superseded run, 15
  in 058, 14 in 105); the affected functions show as "no distinguishing input found".

## Claimed verdict theorems (54 equivalent)
- Axioms (axcheck.py --leanpath, fresh process per module, 13 jobs): 108/108 theorem names exactly std (54
  VOEquiv.<unit>.equivalent + 54 VOEquiv.<unit>.changed_only_where_old_unsafe); axioms/o<order>/axcheck.tsv.
- Kernel replay (tools/t3_replay_jobs.py + leancheck1lp.sh, pjobs_v3 N = 2): import closures of the 54 VOEquiv modules
  through lean_cert (Gen, VOEquiv, VerifOrch), cirlean ffab71e (CIR) and equiv-lean b171660 (EquivLean): 197 jobs (56
  shared CIR/EquivLean modules once, 141 per commit), 197/197 rc 0. Closures per commit: 62 modules (11 commits), 74
  (142), 83 (72), 92 (50); every module of every closure rc 0 (replay_closure_verdicts.tsv). Order 72 (cf3): its 14
  equivalent certificates are the re-run home-TU ones (seed held only unknowns; checks/t3cf3-20261026/NOTE.md).

## behaviour_changed witnesses (38)
- C/C++ (21): see witness/WITNESS_FACTS_C_CPP.md (both outcomes and the input facts for each). All 21 re-run from the
  copies with vo_cert_check.sh: "VOW DIFF", elab rc 0, leanchecker rc 0, old/new = the ci.json records (recorded strings
  stop at 600 characters; the re-run output extends each prefix). Groups by what the difference rests on:
  - only an unmodelled GLib call in the new version: 11 (g_object_ref), 24 (g_type_check_class_cast);
  - GObject class init not having run in the witness memory: 24, 30;
  - identical function source, layout of a class changed in the commit: 50 (TNonblockingServerSocket(int),
    (int,int,int)), 58 (onewayComplete, parseStatusLine), 72 (8 THeaderTransport reads: new reaches an indeterminate
    read in the witness block);
  - a new member written or destroyed: 50 (TNonblockingServerTransport ctor and dtor, config_);
  - source-level changes on ordinary-looking inputs: 77 (parseStatusLine resets closeAfterResponse_), 111 (matchName
    "a.b" vs "a.*": true -> false), 143 (readEnd resets the message-size counters), and 129 (skip(T_UUID): throw ->
    readUUID; the semantics shows UB only because the witness protocol's vptr is null).
- Java (17): each verdict module re-elaborated from the copy (tools/java_witness_rerun.sh: lean_eqj + equiv-lean
  751764f + JimpleLean 0149Z): equiv_jimple fails with "the two methods end differently on 12 of 12 sampled inputs
  ... e.g. arguments ..." and the arguments text equals the record's witness for 16; for 29
  FrameBufferState.$values() the record's text stops after the target part and the re-run text extends it (17/17).
  Witnesses (record wording "the rendered results are the same: the final states differ" unless noted):
  - 29: AbstractNonblockingServer$1.<clinit>() (static init); FrameBuffer.changeSelectInterests(), close(), read() on a
    receiver FrameBuffer@0 with default fields (both throw NullPointerException; final states differ);
    FrameBufferState.$values() (both return the 8 enum constants; differs); FrameBufferState.<clinit>() (static init).
  - 41: TBaseHelper.<clinit>(); TProtocol.lambda$readMap$0(int) at -70 (both return a HashMap).
  - 71: TFastFramedTransport$Factory.<init>() / (int) at -340 / (int,int) at -340, -362; TFramedTransport$Factory.<init>()
    / (int) at -70 (constructors on a fresh factory object).
  - 115: AutoExpandingBufferReadTransport.consumeBuffer(277), TMemoryInputTransport.consumeBuffer(277) on a fresh receiver.
  - 118: TProtocolUtil.setMaxSkipDepth(-70). 119: TProtocolUtil.<clinit>().
  The statement's domain is "receiver and reference arguments non-null, any heap", so receivers come with default
  (null/zero) fields: the three FrameBuffer NPE witnesses use such a receiver, which FrameBuffer's own constructor does
  not produce; the <clinit> witnesses are the JVM's own static-init runs; the negative sizes go through public
  constructors and a public setter.

## Scans of the 54 claimed closures (both versions; checks/cirpun-20261025's tool copy, controls pos/neg PASS)
- cirpun f365f63 (tools/cirpun_claims.py; 108 jobs = 54 units x old/new unit.cir, root = the unit): 74 clean; 34 with
  rows, all in 6 distinct functions:
  - TEvhttpServer::complete (claimed in 11 commits; 22 jobs; closure 37): FLAG 24 = 14 library-result reads (the ostream
    returned by the ostreamOut model, TEvhttpServer.cpp:137/143/151), 8 unresolved virtual calls in shared_ptr's control
    block (_Sp_counted_base::_M_release / _M_release_last_use: 4 vptr loads + 4 indirect calls), and 2 dyn=rec loads of
    the two 32-bit use/weak counters as one 64-bit value in _M_release (shared_ptr_base.h:336; libstdc++'s combined-count
    fast path), reached through RequestContext's shared_ptr members: other (type-punned load in the C++ library code).
  - TNonblockingIOThread::setCurrentThreadHighPriority and ::breakLoop (142; closures 1 and 8): FLAG 1 each, a
    library-result read of *__errno_location() (TNonblockingServer.cpp:1463, 1328).
  - TFileTransport::~TFileTransport (142; closure 31): FLAG 23 = unresolved virtual calls (TFileTransport.cpp:125, 135,
    915; TFileTransport.h:174; shared_ptr control block), 2 dyn=rec 64-bit loads of the shared_ptr counters
    (shared_ptr_base.h:336), 1 errno result read (TFileTransport.cpp:162), the destructor's base-class vptr store
    (TFileTransport.cpp:125), 2 s64 loads through unknown pointers (TFileTransport.cpp:125); CHAR 6 = u8 accesses to
    atomic<bool> in __atomic_base<bool>::store (atomic_base.h:477; 3 rec, 3 arr); ASSUME 1 (root object typed
    TFileTransport).
  - TSocket::setNoDelay, setKeepAlive, setLinger (142; closure 52): FLAG 12 = 9 ostreamOut library-result reads in
    getSocketInfo (TSocket.cpp:833-843), 2 char_traits<char>::assign accesses through an unknown pointer, 1 errno read
    (e.g. TSocket.cpp:755); NOOBJ 3 in basic_string internals (basic_string.h:266, 299, 1280). All inside
    getSocketInfo(), which these setters call only when setsockopt returns -1 (TSocket.cpp:752-756): error path.
- memcpy (tools/memcpy_claims.py, same jobs): 102 jobs without a memcpy in the closure; 18 sites, all in the 6
  TSocket setter jobs (3 per job): TSocket::setCachedAddress (TSocket.cpp:938 and 944), memcpy into the member
  cachedPeerAddr_.ipv4 / .ipv6 from the caller's sockaddr (a local sockaddr_storage in getPeerHost/getPeerAddress,
  TSocket.cpp:867/905, or the addrinfo result, line 410): distinct objects; and std::char_traits<char>::copy (string
  copy between distinct buffers). Reached from the setters only through getSocketInfo on the error path.

## Java and Rust checks
- Double/Float.compare reachability (tools/jcompare_t3.py, my T3 variant of jcompare_claims.py that follows
  org.apache.thrift calls): the 17 Java witness functions in both versions: 34 rows, methods found in all, 0 hits;
  controls TBaseHelper.compareTo (hit) and TCompactProtocol.writeMapEnd (none) as expected in all 12 runs. No Java
  equivalent verdicts exist. (A first run had an enum-header regex error; kept as jcompare_t3_v1_enum_bug.txt.)
- Rust: 0 kernel verdicts; crate-type cases as listed under unknown reasons.

## Spend and compute
- Records: model $164.96 (C++ $156.22, C $8.74, Java and Rust $0), 157.90 core-h (record core_seconds; per language, by_language core + prepass core seconds: C++ 69.4, C 15.6, Java
  48.0, Rust 24.9) = summary.
- Usage logs (96 files in runs/ incl. .crash_* dirs): 1,672 calls, $189.77 (kept run dirs 1,356 calls $164.96;
  crashed/superseded dirs 316 calls $24.81) = summary; under the $300 cap. The 21:51Z prune of orders 131-150 build dirs
  did not change these totals.
- 072's pre-cf3 run (superseded/cf3_20261026T2008Z/072_c98e79ad9f14_cpp.guard.log, several guards in one file): largest
  metered value 81,777 core-s = 22.716 core-h at 20:18:26Z; veriforch reported 22.404. Total 157.90 + 22.72 = 180.62 core-h
  (veriforch: 180.3).
- Deviation marks: by_language.*.cf3 = true on orders 72 (C++), 90, 103 (Rust); cf1/cf2 are not marked in records
  (LAUNCH_NOTES: resumes 2026-10-25T21:32Z/21:33Z; cf1 moved order 33's record aside and re-ran it).

## Questions for producers
- 072's superseded guard log: which line gives 22.404 core-h (the largest metered value is 22.716)?

## Disclosures
- My first Java re-run put its output dir first on LEAN_PATH, which shadowed VOEqJ (all 17 failed to load); fixed and
  re-run (first outputs kept in witness/java_rerun_v1_shadow_bug). The witness-file matcher needed two parser fixes
  (v1, v2 kept in tools/). The scheduler runs and every job ran under coreh_guard_v2; small analysis scripts under g1.sh.
- Compute of this check: 0.21 core-h (replay 0.108, axioms + witnesses 0.027 + 0.066, scans 0.013), N <= 2.
