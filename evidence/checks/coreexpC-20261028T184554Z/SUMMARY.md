RESULT: no claimed C/C++ closure outside sec-ub reaches a site where a condition of the reported library-model gaps
(the C maintainer session/cjlemmas FINDINGS.md 4742f16c9e67cd52: G1-G35 without va_arg types and sscanf, M1, M2) can hold. 541 job rows
(17 study labels + the Adler-32 port) were screened; 42 source-level sites of the gap kinds lie inside closures (8
printf-family calls, 16 memory-function ops, 5 atomic sites, 3 bit-field reads, 11 const-local candidates), and at each
one the gap's condition is excluded by the CIR (constant size, guard, literal format with matching argument types,
valid order, initialization-only use). No va_start/va_end/va_copy/va_arg, __cxa_guard or static-local, VLA, atexit/exit
call or cmpxchg lies in any closure.

# Check by an agent: exposure of the cirlean library-model gaps (fork of the evidence-owner session; stamp 20261028T184554Z; written 2026-10-28T19:00:58Z by date -u)

## Scope and method
- Jobs (tables/jobs_all.tsv, 540 rows; + tables/jobs_F_adler.tsv): cirpun-20261025 job lists c2_jsmn (10), c2_trc (121),
  d1_tinyxml2 (28), d1_zlib (14), d2_tinyxml2_rerun (40), trx (4); scancov-20261027T0424Z t4 (1 job, 24 roots), t2rc (3),
  musl (2); t2-20261026T0321Z jobs_t2_c.tsv (102: t2_C 21, t2_Cpp 81); t3-20261026T2147Z jobs_t3.tsv (108: old/new 54
  each); D2 zlib re-run (24) and held-out (11) from vo2zr/vo2zh cirpun/run.out with the replay lib/*.cir (w0 = w1 =
  re-run = held-out, sha 75fea398f852); D2 tinyxml2 held-out (36 units, from vo2txh coverage_tx_d2heldout.txt) run on
  both worker files (w0 66c4368718debaa2, w1 c2146d7b5d909115); extra: the Adler-32 port (replay/adler32-20261027T0854Z
  .../zlib_adler32/adler32.cir = the unified copy, 6956d8e281b88f38; every defined function as root).
  Outcomes covered: proved, proved_model_stated, conditional, partial, refuted, equivalent, refinement. Not covered (per
  brief): UB-finding rows (b), C1 (security-fix study, no claimed verdict), the cJSON and yajl-ruby harness closures.
- scripts/scan.py parses each CIR file once (functions, direct calls, function addresses, sites of the gap kinds,
  #loc source locations) and builds each job's closure from its roots: direct calls plus functions whose address a
  closure function takes; indirect calls are counted, not resolved. Runs: scripts/run_scan.sh (one process at a time,
  ulimit -v 32 GiB, timeout 600 s each); outputs out/<group>/{sites,closures}.tsv.
- Closure check against cirpun's: cirpun-20261025 rows 216/217 equal; the one smaller is d1_zlib inflateCopy (cirpun 4,
  here 2: the zalloc/zfree pointer targets zcalloc/zcfree, which call only malloc/free, no site of any gap kind); T2/T3
  210/210 matched, 184 equal, 26 larger here (address-taken functions), none smaller
  (tables/cirpun_closure_sizes_t2t3.tsv). Parse self-check: scripts/selfcheck.py on the largest T2 file counts 1279
  defined + 92 declared functions = grep's 1371.
- Controls (out/Z_control): the scanner, run on planted programs (libsnd-20261028T184506Z/probe/d0l_cases.cir and
  syntax/t_c.cir, t_cpp.cir written here), reports every planted kind: memcpy/memset ops and a memcmp call, sprintf
  calls, va_start/va_arg/va_end, a VLA (size(%n)), __cxa_guard calls and static-local accesses, an atomic load, a
  const local stored twice and a const local whose address escapes into a pointer that is stored through.

## Per-study counts (tables/per_study.tsv; distinct file:line sites inside closures)
    study                   jobs  closure_fns  indirect_calls  printf  mem0  va  guard  atomic  bitfield  vla  const  exit  condition_can_hold
    c2_jsmn                 10    10           0               0       0     0   0      0       0         0    0      0     0
    c2_trc                  121   481          0               0       0     0   0      0       0         0    0      0     0
    d1_tinyxml2             28    40           9               2       1     0   0      0       0         0    0      0     0
    d1_zlib                 14    20           3               1       3     0   0      0       0         0    0      0     0
    d2_tinyxml2_heldout_w0  36    73           5               0       1     0   0      0       0         0    2      0     0
    d2_tinyxml2_heldout_w1  36    73           5               0       1     0   0      0       0         0    2      0     0
    d2_tinyxml2_rerun       40    63           9               3       1     0   0      0       0         0    2      0     0
    d2_zlib_heldout         11    14           0               1       0     0   0      0       0         0    0      0     0
    d2_zlib_rerun           24    37           22              1       1     0   0      0       0         0    0      0     0
    musl                    2     2            0               0       0     0   0      0       0         0    0      0     0
    t2_C                    21    27           3               0       0     0   0      1       0         0    0      0     0
    t2_Cpp                  81    403          19              1       7     0   0      10      0         0    6      0     0
    t2_recheck              3     3            0               0       0     0   0      0       0         0    0      0     0
    t3_new                  54    758          51              3       6     0   0      27      0         0    5      0     0
    t3_old                  54    758          51              3       6     0   0      27      0         0    5      0     0
    t4_cpp                  1     58           6               0       3     0   0      0       3         0    1      0     0
    trx                     4     50           0               0       0     0   0      0       0         0    0      0     0
  (kinds: printf = printf family incl. TOutput::printf call sites; mem0 = memcpy/memmove/memset/memcmp; va; guard =
  __cxa_guard/static local; atomic; bitfield; vla; const = const-local write/escape/call candidates; exit = atexit,
  at_quick_exit, __cxa_atexit, exit family.) adler32_port: 5 functions, 0 sites.

## Sites and why the gap condition cannot hold (tables/sites_unique_by_source.tsv)
- printf family, G1-G7, G34, M2 (argument C types, %ls/%lc, * width, %u of a negative int), G8-G10 (overlap), G11
  (stream): all 8 call sites have literal formats (tables via scripts/printf_fmt.py and the string globals):
  TNonblockingServer.cpp:1422 "IO thread #%d exiting with error." (int), :1425 no conversion, :1461 "IO Thread #%d
  using high-priority scheduler!" (int) [T3; TOutput::printf is only declared in that unit, its body (va_start/vsnprintf)
  is in no closure]; TOutput.cpp:98 fprintf(stderr, "Thrift: %s %s\n", char*, char*) [T2; stream = load of stderr];
  gzlib.c:557 snprintf(state->msg, n, "%s%s%s", char* x3) [D1/D2 zlib; destination freshly allocated]; tinyxml2.cpp:573
  "%d" (int), :600 "%.17g" (double), :607 "%lld" (long long, !s64i) [D1/D2 tinyxml2]. Every conversion matches its
  argument's type; no %lc, %ls, *, %u or %.Ns; formats are string literals, so the destination cannot be the format.
- memory functions, G12-G15 (null pointer with n = 0): sizes are constants (TNonblockingServer.cpp:1445 memset 4;
  TUuid.h:53 memcpy 16; inflate.c:1465/1466 memcpy 112 and 7160; libc++ string:880 memcpy 24, :945/:984 memset 24), or
  guarded (char_traits.h:417/429 return when n == 0; stl_uninitialized.h:1343 only when count > 0; TSocket.cpp:938/944
  only when len == 16 / 28; inflate.c:1476 only when window != NULL, n = 1 << wbits), or at least 1 (tinyxml2.cpp:206
  len + 1; infback.c:334 copy after PULL/ROOM with length != 0); tinyxml2.cpp:342 memcpy(q, buf, len) has a local
  array and a buffer position as pointers, so no null pointer.
- atomics, G27-G29: atomicity.h:68/73 fetch-add acq_rel, shared_ptr_base.h:336 load acquire (the 64-bit counter load
  already discussed in the paper), thrift_struct.c:23 load seq_cst are valid orders; atomic_base.h:477
  (__atomic_base<bool>::store with a run-time order; CIR has its relaxed/release/seq_cst variants) is called only from
  __atomic_base<bool>::operator=, with the constant 5 (seq_cst). No cmpxchg in any closure.
- bit-fields, G30-G31: only reads (libc++ string:2053/2125/2146, T4); no set_bitfield in any closure; the string
  representation is written whole (memset/memcpy of 24 bytes above) or given by the theorem's hypotheses.
- const locals, G35: candidates digitScaled, digit (tinyxml2.cpp:532/556), delta, toPrint (2698/2721), buflen (GetStr),
  byte (TCompactProtocol.tcc:226, T4 writeByte: the bitcast address goes to the transport's write, a read),
  __diffmax (std::min by const reference, a read), priority, __how_much: every store is the initialization (once per
  loop iteration for the loop-scoped ones); the other matches are SSA names reused in sibling regions (operand types
  are values, not the alloca's pointer).
- va_list (G20-G25), __cxa_guard (G26), exit handlers (M1): no such site in any closure (va ops exist in 15 scope files,
  92 ops, e.g. TOutput::printf, gzprintf, the Thrift compiler's main, all outside the closures). VLA (G32-G33): no
  dynamic alloca in any of the 220 scope files (tables/all_files.txt; the Adler-32 file's closure has no site at all).

## Limits
Static screen of CIR closures; virtual and other indirect calls are not followed (counted per study above; the same
calls cirpun leaves unresolved: theorem hypotheses for T4's transport, not scanned in T2/T3 per the paper). Invalid
atomic orders that clang erases (G27/G28 with literal orders) leave no op in CIR; the only run-time-order atomic store in
the closures receives seq_cst from its one caller. Not screened (outside the job lists): the other equiv-lean example
CIR files (eq-*/examples/cir a..v), the cJSON/yajl harness closures, UB findings, C1.
