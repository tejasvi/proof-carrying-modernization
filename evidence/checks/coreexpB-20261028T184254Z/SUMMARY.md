RESULT: controls PASS. Stride screen: 0 sites where the traced object's element size differs from the pointee size, among 1,801 pointer-arithmetic sites in the closures of all 506 claimed job rows (16 studies); 140 sites have an untraced origin behind a size-changing cast, of which 2 reach a root parameter of another size (musl strlen.c:17, the word loop; T2 c_glib thrift_protocol_get_instance_private) and 2 per T3 version are byte strides over C++ objects (TFileTransport destructor, TNonblockingIOThread::notify). Union screen: 29 of 177 union member pointers are kept beyond a member access expression, all in libstdc++ std::string (T2, T3) and Thrift TSocket's cached address (3 T3 verdicts); 3 bit-field reads go through a union member in T4's libc++ std::string. The C maintainer session's "member access expressions only" holds for the c_glib union units, not for these.

# Check by an agent: independent static screens for the stride defect and the union gaps U1/U2 (fork of the evidence-owner session)
Written 2026-10-28T18:59:00Z (date -u). Out dir: checks/coreexpB-20261028T184254Z. Scripts: scripts/screen.py (sha8 5b7ae17e; own CIR parser,
region-scoped SSA resolution), scripts/interproc2.py (sha8 ed8b30dc; transitive caller pass), scripts/castcount.py (sha8 a1a38853).
Superseded drafts kept as scripts/screen_v1_nscope.py.txt (SSA names resolved without region scope: gave false
MISMATCH in tiny-regex-c, e.g. re_matchp %19 defined twice in sibling regions) and scripts/screen_v2_noelem.py.txt (no
cir.get_element sites).

## Inputs
- Claimed closures: all_jobs.tsv = 506 rows of 14 job lists: cirpun-20261025 jobs_{c2_jsmn,c2_trc,d1_tinyxml2,d1_zlib,
  d2_tinyxml2_rerun,trx}.tsv; scancov-20261027T0424Z/{t4,t2rc,musl}/jobs_*.tsv; t2-20261026T0321Z/scans/jobs_t2_c.tsv;
  t3-20261026T2147Z/scans/jobs_t3.tsv; vo2zr-20261025T2256Z, vo2zh-20261026T0526Z, vo2txh-20261025T1814Z cirpun/jobs.tsv.
  235 CIR files (all_cir_files.txt), all present. Closures: direct calls from the rows' roots, static functions
  resolved inside their file ("file$name" roots); 506/506 closures built, no missing root (tables/g?.closures.tsv,
  per-unit function lists tables/g?.unitfuncs.tsv).
- Excluded: jobs_b (UB findings), jobs_c1 (security-fix verdicts, cJSON), the cJSON and yajl-ruby harness closures, R2
  directories. Nothing under them was opened.

## Controls (controls/CONTROL_VERDICT.txt): PASS
- Stride: stride-20261028T182920Z/probe/d0_cases.cir: MISMATCH for c_char_stride, c_short_stride, c_char_diff,
  c_int_over_struct, c_char_over_struct, c_heap_char_stride, c_wide_over_char; none for c_same_size, c_plain,
  c_heap_int_index; probe/s_f7.cir: MISMATCH for t_char_stride and t_short_stride.
- Union: coresnd-20261028T183958Z/probe/d0s_cases.cir: u1_stale and u1_stale_ints KEPT (member pointers stored in
  locals), c_union_expr EXPR, u2_bits_after_float: 2 bit-field ops on a union member record.

## Method
S: every cir.ptr_stride, cir.ptr_diff and cir.get_element; each pointer operand is traced inside its function through
casts, strides, element and member addresses, allocas, globals, allocation calls (heap objects typed by their first
cast) and loads of non-escaping local slots (all values stored into the slot). Classes: MISMATCH (traced object's
element size differs from the pointee size), SAME, UNKNOWN_NOCAST / UNKNOWN_CAST (untraced origin: parameter, memory
load, call result; with or without a size-changing pointer cast on the traced path). Parameter origins are then
followed through direct callers in the study's closures (depth <= 12) to objects or root parameters (tables/ip2.*).
castcount: size-changing pointer bitcasts per study (allocation results excluded; tables/cc.*).
U: every cir.get_member on a union: EXPR if every use is the address of a load, store, member or bit-field op later in
the function with no access to another member of a union of the same type in between; else KEPT. U2: bit-field ops
whose address chain passes through a member of a union.

## Results (tables/per_study.tsv; totals tables/totals.txt; sites tables/g?.S.tsv, g?.U.tsv, g?.U2.tsv; candidates
tables/candidates.tsv)
    study                units  functions  S_sites  SAME  UNKNOWN_NOCAST  UNKNOWN_CAST  MISMATCH  param_sites  ROOT_SAME  P_SAME  P_UNKNOWN  ROOT_CAST  P_MISMATCH  size_changing_casts  U_sites  U_EXPR  U_KEPT  U2_union_member_bitfield_ops
    c2_jsmn              10     10         0        0     0               0             0         0            0          0       0          0          0           0                    0        0       0       0
    c2_trc               121    283        1241     357   884             0             0         884          177        0       707        0          0           0                    99       99      0       0
    trx                  4      17         83       24    59              0             0         56           16         0       40         0          0           0                    6        6       0       0
    musl                 2      2          135      0     0               135           0         135          134        0       0          1          0           46                   0        0       0       0
    t4_cpp               1      58         12       7     5               0             0         0            0          0       0          0          0           4                    6        6       0       3
    t2_recheck           3      3          0        0     0               0             0         0            0          0       0          0          0           0                    6        6       0       0
    t2_C                 21     21         1        0     0               1             0         1            0          0       0          1          0           7                    0        0       0       0
    t2_Cpp               81     402        12       1     11              0             0         2            0          0       2          0          0           19                   22       13      9       0
    t3_old               54     614        41       1     38              2             0         14           2          1       11         0          0           44                   17       7       10      0
    t3_new               54     614        41       1     38              2             0         14           2          1       11         0          0           44                   17       7       10      0
    d1_tinyxml2          28     34         2        1     1               0             0         0            0          0       0          0          0           0                    0        0       0       0
    d1_zlib              14     18         17       11    6               0             0         0            0          0       0          0          0           13                   4        4       0       0
    d2_tinyxml2_rerun    40     58         34       6     28              0             0         27           21         5       1          0          0           1                    0        0       0       0
    d2_tinyxml2_heldout  38     53         48       2     46              0             0         22           2          5       15         0          0           0                    0        0       0       0
    d2_zlib_rerun        24     27         129      22    107             0             0         13           13         0       0          0          0           20                   0        0       0       0
    d2_zlib_heldout      11     14         5        0     5               0             0         2            2          0       0          0          0           10                   0        0       0       0
- S, untraced behind a cast (140): musl 135 = 130 byte strides of memcpy over its void* parameters (typed as character
  arrays by the theorems' hypotheses; transitive: root parameters of pointee size 1) and 5 strlen sites, among them
  strlen.c:17, w++ on const size_t * over the character array (the word loop; transitive ROOT_CAST: the root's char
  parameter); t2_C 1: thrift_protocol_get_instance_private, thrift_protocol.c:42, a u8 stride over the _ThriftProtocol
  instance by the private offset (the function is the root of unit 409, proved_model_stated; ROOT_CAST); t3_old and
  t3_new 2 each: TFileTransport.cpp:125 in TFileTransport::~TFileTransport (this cast to u8 and moved by a virtual-base
  offset loaded from the vtable; the verdict for that destructor) and TNonblockingServer.cpp:1337 in
  TNonblockingIOThread::notify (pos += ret over the bytes of the local pointer conn; in the closure of the breakLoop
  verdict). Under the stride defect, each of these moves by elements of the object reached, not bytes.
- No size-changing pointer cast at all in the closures of c2_jsmn, c2_trc, trx, d1_tinyxml2, d2_tinyxml2_heldout and
  t2_recheck: their pointers cannot reach an object of another element size except through pointer values stored and
  reloaded under another type (a punning case, outside this screen).
- U KEPT (29): basic_string.h:222 (libstdc++ _M_local_data, the SSO buffer pointer, returned and kept in _M_p; and the
  move constructor): 9 in t2_Cpp (in the closures of 9 T2 C++ units), 6 per T3 version (5 + 3 verdicts reach
  _M_local_data and the move constructor); the union's other member (_M_allocated_capacity) is accessed by member
  expressions in the same closures (capacity, _M_dispose, _M_capacity). TSocket.h:362-363 (4 per T3 version):
  setCachedAddress copies into &cachedPeerAddr_.ipv4 / .ipv6 (cir.libc.memcpy), getCachedAddress returns them cast to
  sockaddr*; 3 T3 verdicts per version (setNoDelay, setKeepAlive, setLinger) reach both. A KEPT pointer is what U1
  needs; whether a stale value is read depends on the run-time order of member accesses, which this screen does not run.
- U2 (3): T4's libc++ std::string: __is_long reads __rep_.__s.__is_long_, __get_long_cap reads __rep_.__l.__cap_,
  __get_short_size reads __rep_.__s.__size_ (string:2053, 2146, 2125), each a bit-field of one member of the __rep_
  union; under U2 such a read gives 0 for bits written through the other member, so the long/short decision of a
  string written as long reads as short. Whether a T4 theorem reaches a long string depends on its hypotheses.
- c_glib unions (t2_recheck thrift_bitwise_cast_*): 6 EXPR, no KEPT, as the C maintainer session says.

## Limits
Static and intra-procedural except the caller pass (direct calls only; indirect and virtual calls unresolved);
memory-loaded pointers stay unknown (787 parameter-origin sites end there); heap objects are typed by the first cast
of the allocation; record sizes computed from the CIR types (natural alignment, packed honoured); no program is run.
