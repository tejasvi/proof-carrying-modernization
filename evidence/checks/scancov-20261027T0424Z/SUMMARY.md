RESULT: coverage of the punning scan (cirpun f365f63) and the memcpy-site check over the claimed C/C++ theorem sets is complete after this check; three sets had no scan (T4's C++ side, the T2 re-check at e6ac99a, the musl library-model refinements). T4 C++: 13 flags, all unresolved virtual calls through the transport and protocol objects plus one byte read typed by the read contract, no access of another width; memcpy none in the closure. T2 re-check: no flag; no memcpy in the files. musl: strlen's word loop (64-bit loads over a char array) is on paths musl_strlen_refines covers, so that theorem holds only for cirlean's one-element reading; memcpy's word paths are excluded by musl_memcpy_refines's WordFree hypothesis; no memcpy call sites. The limits paragraph's "one access of another width" must become two (shared_ptr release in T3; musl strlen's word loop).

# Scan coverage of the claimed C/C++ theorems (an agent, fork of the evidence owner; 2026-10-27 04:24Z-04:55Z)

Check dir ~/fv_paper/evidence/checks/scancov-20261027T0424Z; copies in ~/fv_paper/replay/scancov-20261027T0424Z (tool/ =
cp -rL of checks/cirpun-20261025/tool, 0 symlinks, its SHA256SUMS 10/10 OK in both; t4/, t2rc/, musl/ = copies of the IR
files scanned). Every job ran under coreh_guard_v2 with logs in guard/ (10 jobs, 1.2 core-s metered in all).

## Coverage table (evidence for each claimed C/C++ theorem set)
- Migration C-to-Rust, tiny-regex-c (TRX): cirpun-20261025 trx 4/4 clean; memcpy-20261025: no memcpy in the files.
- jsmn port (R5; equiv-lean 373874f, jsmn 25647e6): checks/r5jsmn-scan-20261026, 7 functions, all counts 0; jsmn_run.cir has
  no memcpy (grep 0).
- C1 / C1b: cirpun-20261025 c1 (18/22 clean, localeconv reads); memcpy-20261025 c1. C1b adds no claims.
- C2 (tiny-regex-c, jsmn): cirpun-20261025 c2_trc 121, c2_jsmn 10; no memcpy in the files.
- D1 zlib, D1 tinyxml2, D2 tinyxml2 re-run: cirpun-20261025; memcpy-20261025.
- D2 zlib re-run / held-out, D2 tinyxml2 held-out: vo2zr, vo2zh, vo2txh; memcpy: D2 zlib on the excluded path, held-out none.
- cJSON harness theorem (266d1ed): cjh-20261025T1854Z/cirpun; memcpy-20261025 (cjh jobs).
- whole cJSON harness (c4ef58d): fh-r1-* (FLAG 2 typed localeconv reads, NOOBJ 2 guarded); yj-r3-extra .../memcpy (2 sites).
- yajl-ruby harness: yj-r3-extra-20261026T2154Z (inconclusive: unidentified objects); yj-r3-extra .../memcpy (5 sites).
- UB cases (B): cirpun-20261025 b; memcpy-20261025 b.
- T2: t2-* (91/102 clean); one memcpy site, distinct objects.
- T3: t3-20261026T2147Z (74/108 clean; shared_ptr counter load in 12 verdicts); 18 memcpy sites, distinct, error path.
- T3 re-run of the 12 (e6ac99a): t3sp-20261027T0244Z, cirpun output byte-identical to T3; same closures as T3.
- T4, C++ side (equiv-lean ac65118, cirlean 28e2380): NONE before this check -> section 1.
- T2 re-check, units 132/254/566 (e6ac99a): NONE -> section 2.
- musl strlen/memcpy refinements (equiv-lean 65c47df): NONE -> section 3.
- Not claim sets: the LLVM test programs (V; differential outcomes, in their own paragraph), the harness seed sweep.
Controls (copy): run_controls.sh -> pos PASS (FLAG 13, CHAR 3, NOOBJ 1, ASSUME 1), neg PASS (all 0) (controls.out).

## 1. T4, C++ side
- IR: ~/veriforch/runs/t4gen_cpp/v0/TTransportInst/unit.cir (sha256 b3ad9875411e6294..., copied to t4/unit.cir), the source
  that EquivLean/Demo/Gen/Cir/Thrift/ProtoTT.lean names (manifest.json "source"); all 459 body functions of the manifest
  are defined in the file (t4/manifest_body_syms.txt vs t4/cir_func_syms.txt, 0 missing).
- Roots: the 24 functions of the generated module that the T4 C++ proofs reference (grep of EquivLean/Demo/Thrift/Cpp/*.lean
  in replay/eqt4-20261026T0559Z; t4/roots_map.tsv): readVarint32/64, readByte, readI16, readFieldBegin, readListBegin,
  readSetBegin, getTType, getCompactType, getMinSerializedSize, checkReadBytesAvailable(TList&), writeByte, writeI16,
  writeVarint32/64, writeFieldBeginInternal, writeCollectionBegin, writeBinary, the zigzag conversions, TList and
  TProtocolException constructors.
- cirpun (t4/cirpun.tsv): closure 38 functions; FLAG 13, CHAR/SIGN/AGG/NOOBJ/ASSUME 0. The 13 rows:
  - 12 = 6 virtual calls, each a vtable-pointer load and an indirect call with an unresolved target: TTransport::write,
    readAll, borrow, consume (TTransport.h:164, 132, 231, 246), trans_->checkReadBytesAvailable (TCompactProtocol.h:154) and
    the protocol's own virtual checkReadBytesAvailable(list) (TCompactProtocol.tcc:589). In the theorems the transport calls
    are hypotheses (ReadContract, WriteContract, EofContract, CheckContract in Cpp/Transport.lean, Eof.lean, ListRead.lean,
    stated on the dispatch functions), and the protocol's vtable is fixed to TCompactProtocolT's by vtProto
    (ListRead.lean:77), whose checkReadBytesAvailable is in the closure.
  - 1 = a u8 load of borrowed[rsize] (TCompactProtocol.tcc:770) from the pointer borrow returns; ReadContract.borrow states
    that this pointer is into a block of type array of u8 (Transport.lean:81-96), so the read has its object's width.
  - No access of another width on an object whose type the program or the statements fix.
- memcpy (t4/memcpy.tsv): one memcpy in the file, none in the 38-function closure (closure matched in full).

## 2. T2 re-check (units 132, 254, 566 at cirlean e6ac99a)
- IR: the units' unit.cir (copies of replay/t2union-20261027T0208Z/run_<order>/v0/...: 0132 ffac8bd6, 0254 e4ae3f3c, 0566
  4e9d99ac); roots thrift_bitwise_cast_guint64 (132, 566) and thrift_bitwise_cast_gdouble (254).
- cirpun (t2rc/cirpun_<order>.tsv, --all): closure 1 function each; all flag counts 0, OK 6 each. The scan is
  field-sensitive: the union's members are distinct fields (f0 u64, f1 double), each accessed with its own type. The union
  read itself (write one member, read the other) is governed by the semantics' union rule, stated in the paper for e6ac99a.
- memcpy: no memcpy in any of the three files (t2rc/memcpy.tsv).

## 3. musl library-model refinements (equiv-lean 65c47df, cirlean 28e2380)
- IR: examples/cir/musl/strlen.cir (bd569675...) and memcpy.cir (b8013b3e...) of replay/eqmusl-20261025T2100Z/equivlean
  (new files of that commit, checks/eqmusl-20261025T2100Z/new_files.txt); roots musl_strlen, musl_memcpy.
- strlen (musl/cirpun_strlen.tsv): FLAG 4 = u64 loads over the char array in the word loop (strlen.c:17, dyn arr), CHAR 4 =
  byte loads of the alignment and tail loops (strlen.c:16, 20) on the same root object, ASSUME 1 (root used as s8 and u64).
  musl_strlen_refines (StrlenRefines.lean:62) has no hypothesis that keeps the word loop from running (hblk, hb, hwf, hlen,
  hmodel, hchar only), and the module doc (lines 13-17) states that in cirlean (<= 28e2380) a size_t load at a char element
  reads that one element, so the word loop sees one character per word: "The result is still the model's; this is
  cirlean's semantics of type-punned scalar accesses ..., not the machine's." This claimed theorem's covered executions
  include an access of another width, read with the one-element meaning.
- memcpy (musl/cirpun_memcpy.tsv): FLAG 44 = u32 loads and stores on the u8 arrays in the word and shifted-word paths
  (memcpy.c:27-96), CHAR 84 = byte accesses to the same root objects, ASSUME 2. musl_memcpy_refines (MemcpyRefines.lean:89)
  assumes WordFree (musl's word paths do not run) and a destination in another block, so every flagged access lies on a
  path its hypotheses exclude; the word paths are the separate difference musl_memcpy_ne_model (MemcpyCex).
- memcpy-site check: no call to memcpy in either file (musl/memcpy.tsv).

## Change the paper needs (sec-limits.tex, paragraph "A defect of the C semantics")
- Replace "finds one access of another width in their call graphs. When libstdc++ releases ... reads that access." by:
  "finds two accesses of another width on paths that the theorems cover. When libstdc++ releases a shared_ptr, it reads
  the two 32-bit reference counters as one 64-bit word, and 12 equivalence verdicts of T3 reach this code (Section 8), so
  those verdicts are valid only for the way our semantics reads that access. musl's strlen reads a character array a
  64-bit word at a time, and its refinement theorem (Section 9) holds only for our semantics' reading of those loads, one
  character per word; the word paths of musl's memcpy are excluded by its theorem's hypotheses."
- In the next sentence add T4 to the virtual-call class: "... virtual calls it cannot resolve, whose targets in the same
  translation unit scan clean or, for Thrift's transport in T4, are hypotheses of the theorems; ..."
- The memcpy sentence stays true: T4, the T2 re-check and musl add no memcpy site.
- sec-trust's musl paragraph should say that the strlen refinement relies on the one-element reading in its word loop.

## Disclosures
- Writes only in the two directories above and this fork's progress file; no producer tree written; read-only greps of
  the replay copies and of ~/veriforch/targets/thrift sources for line context. The interim coverage table went to the
  parent session as "main" (the tool refuses the session's own name from inside a fork).
- Compute: 10 guarded jobs, 1.2 core-s metered (under 0.001 core-h).
