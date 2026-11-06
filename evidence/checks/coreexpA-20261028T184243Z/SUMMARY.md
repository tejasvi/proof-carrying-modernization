RESULT: on the claimed C/C++ closures outside sec-ub, no scan row and no CIR site is an instance of G5, G4, G2 or G3. The C maintainer session's bound holds for G5, G4 and G2 by the scanner's own rules (any such access on a known object is FLAG, AGG or CHAR; on an unknown object FLAG), and none of the 833 FLAG/AGG/CHAR rows on claimed paths is of those kinds; G3, which the scanner does not see, is cleared by a direct CIR search.

# An agent (fork of the evidence-owner session), 2026-10-28T18:51:37Z by date -u; dir /home/user/fv_paper/evidence/checks/coreexpA-20261028T184243Z

## Inputs and coverage
cirpun f365f63 outputs (read only): cirpun-20261025 (per-study dirs, all_summary.tsv), scancov-20261027T0424Z (t4, musl,
t2rc), t2-20261026T0321Z/scans, t3-20261026T2147Z/scans, vo2zr-20261025T2256Z, vo2zh-20261026T0526Z, vo2txh-20261025T1814Z;
adler32-20261027T0854Z/cirpun (Adler-32 port: FLAG/CHAR/SIGN/AGG/NOOBJ/ASSUME 0, OK 412, per its SUMMARY.md l.78-80).
Collected by scripts/collect.py (units.tsv: 540 scan files; rows_FAC.tsv: 1,735 FLAG/AGG/CHAR rows); classified by
scripts/classify.py (classes.tsv, classes_per_study.tsv, candidates.tsv). Excluded by brief: b (UB findings), cJSON and
yajl-ruby harnesses (cjh-*, fh-r1-*, yj-*; not opened). Not claimed: c1 (behaviour_changed; no kernel-checked verdict),
vo2txh cirpun/allu_w0.tsv (whole tinyxml2 unit, not a closure). No claimed closure of the listed studies lacks a scan.
Coverage note: the member-strict re-checks (equiv-lean fac6c38) and the T2/T3 second re-checks reuse the same programs;
their scans are the ones above (no separate scan at 424e821).

| set study [class] | units | FLAG | AGG | CHAR |
|---|---|---|---|---|
| cirpun-20261025 b [excluded] | 3 | 3 | 35 | 0 |
| cirpun-20261025 c1 [excluded] | 22 | 8 | 0 | 0 |
| cirpun-20261025 c2_jsmn [claimed] | 10 | 0 | 0 | 0 |
| cirpun-20261025 c2_trc [claimed] | 98 | 0 | 0 | 0 |
| cirpun-20261025 c2_trc [partial] | 23 | 0 | 0 | 0 |
| cirpun-20261025 d1_tinyxml2 [aux] | 1 | 0 | 0 | 0 |
| cirpun-20261025 d1_tinyxml2 [claimed] | 23 | 0 | 0 | 0 |
| cirpun-20261025 d1_tinyxml2 [partial] | 5 | 18 | 0 | 0 |
| cirpun-20261025 d1_zlib [aux] | 1 | 0 | 0 | 0 |
| cirpun-20261025 d1_zlib [claimed] | 14 | 0 | 0 | 0 |
| cirpun-20261025 d2_tinyxml2_rerun [aux] | 1 | 4 | 0 | 0 |
| cirpun-20261025 d2_tinyxml2_rerun [claimed] | 32 | 2 | 0 | 0 |
| cirpun-20261025 d2_tinyxml2_rerun [partial] | 8 | 16 | 0 | 0 |
| cirpun-20261025 trx [claimed] | 4 | 0 | 0 | 0 |
| scancov musl [claimed] | 2 | 48 | 0 | 88 |
| scancov t2rc [claimed] | 3 | 0 | 0 | 0 |
| scancov t4_cpp [claimed] | 1 | 13 | 0 | 0 |
| t2 t2_C [claimed] | 21 | 0 | 0 | 0 |
| t2 t2_Cpp [claimed] | 74 | 1 | 0 | 0 |
| t2 t2_Cpp [partial] | 7 | 41 | 0 | 0 |
| t3 t3_new [claimed] | 54 | 325 | 0 | 6 |
| t3 t3_old [claimed] | 54 | 325 | 0 | 6 |
| vo2txh-20261025T1814Z d2_tinyxml2_heldout [claimed] | 27 | 0 | 0 | 0 |
| vo2txh-20261025T1814Z d2_tinyxml2_heldout [partial] | 11 | 10 | 0 | 0 |
| vo2zh-20261026T0526Z d2_zlib_heldout [claimed] | 10 | 0 | 0 | 0 |
| vo2zh-20261026T0526Z d2_zlib_heldout [partial] | 1 | 0 | 0 | 0 |
| vo2zr-20261025T2256Z d2_zlib_rerun [claimed] | 20 | 19 | 0 | 0 |
| vo2zr-20261025T2256Z d2_zlib_rerun [partial] | 4 | 0 | 0 | 0 |

## Scanner rules that make the bound (cirpun-20261025/tool/src/CirPun.lean)
- classify (l.786-801): unknown or untyped object -> FLAG; scalar access on a record/array object: load -> AGG, 8-bit
  access -> CHAR, otherwise FLAG (G5: store over a whole aggregate, or a load at its root); aggregate access of another
  type -> FLAG (G4). Pointer accesses on pointer objects are OK (any pointee).
- Library-model calls (checkFunc, .call case): every typed pointer argument T* is checked as an access of type T to
  its object (G2: strtol/strtod argument 1 is char**, so an end pointer aimed at a non-pointer object is FLAG; aimed at a
  pointer of another type it is OK, and cirlean stores a pointer value there, which reads back the same).
- Not covered: va_arg results are unknown objects; sscanf/printf formats are not compared with the arguments (G3).

## Claimed-path rows by class (classes.tsv, claimed): 833 rows, 0 candidates
- element width/kind on scalar objects: s64 on s32 (48: libstdc++ shared_ptr_base.h:336 64-bit counter load, a member
  path, in 24 T3 scans = 12 unit ids, 11 TEvhttpServer::complete + 1 TFileTransport D2); s8 on u64 and u64 on s8 (8:
  musl strlen word loop); u32 on u8 and u8 on u32 (128: musl memcpy word paths, excluded by WordFree); u8 on bool (12:
  CHAR, T3). All are the one-element meaning already in sec-limits; none designates a whole aggregate.
- library-model argument, object unknown: 362 (T3, ostreamOut arg 0 = result of the previous ostreamOut call in a
  chained '<<', TEvhttpServer.cpp:130-151 and TSocket.cpp:833-843; typed by the model).
- unknown objects: 37 (T3): errno through __errno_location (12, error paths); std::char_traits<char>::assign s8
  load/store on string-model storage (12); TFileTransport D2 (unit 142): vtable-offset s64 load (2), vptr loads (6,
  'unknown operation'), vptr store into a base subobject (2, 'base class of an object of another type'); T4: u8 load of
  the borrowed buffer (1, typed by ReadContract.borrow); T2 proved unit 194: TOutput function pointer (indirect call).
- unresolved indirect calls (129) and their slot loads (109).
- The T3 vptr store is not G5: at the T3 pin cirlean ffab71e, Eval.lean:446-452 evaluates cir.vtable.get_vptr by
  extending the object's path with ctx.vptrPath, so the store goes to the vptr member (CIR
  ~/fv_paper/replay/t3-20261026T2147Z/runs/142_0835277ec274_cpp/cir/0835277ec274c300bf8935649132d623a93ab172/thrift_transport_TFileTransport/unit.cir:3487,
  source TFileTransport.cpp:125); the scanner flags it only because it cannot name the base-class object.
- The libstdc++ atomics of the T2 sentence are 3 NOOBJ rows (atomicity.h:73/94) in unit 463, and the T2 counter loads
  are in units 189, 193, 463, 532: all five are partial outcomes, not proved theorems (jobs_t2_c.tsv; NOTE.md l.29-31).

## G3 (scripts/g3scan.py, g3_hits.tsv: 532 units, 270 CIR files, reachability over direct calls from the roots)
- va_arg/va_start: in tinyxml2 XMLPrinter::Print and XMLDocument::SetError, zlib gzprintf, Thrift TOutput::printf, T2
  compiler helpers (pdebug, failure, yyerror, ...): reachable from no claimed root.
- scanf family reachable from claimed roots only in two refuted D2 tinyxml2 units, whose roots are the callers: unit 91
  XMLUtil::ToUnsigned ("%x"/"%u" into unsigned*, tinyxml2.cpp:635) and held-out unit 5 XMLUtil::ToInt64 ("%llx" into
  unsigned long long, "%lld" into long long, tinyxml2.cpp:689/696); and in partial unit 84 (ToFloat, "%f" into float*,
  l.669). Conversions and argument types agree. XMLUtil::ToInt ("%x", l.620) and THttpTransport::parseChunkSize are
  reachable from no claimed root. Limit: indirect calls are not followed (their targets: sec-limits' existing sentence).

## Outside this brief (for the parent)
- T3 unit 142 (TFileTransport D2) looks up its virtual base by a byte stride of -24 on the vptr (unit.cir:3474) and a
  byte stride over this (unit.cir:3478). At ffab71e, Mem.stride? (CIR/Memory.lean:133) is none for a vtable pointer, and
  for a path not ending in an array index, whenever n != 0 (elemPos? none), i.e. 'pointer arithmetic out of bounds' on
  that path; relevant to the stride defect and to how the T3 verdict treats this path.
- Excluded set b (UB findings) holds 24 AGG rows (scalar loads at aggregates): sec-ub's.
