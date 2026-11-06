# Pre-registration T: Apache Thrift at scale (coverage, a stratified random sample, CI verdicts, wire-protocol consistency)

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before any model call on Thrift. The user
asked for this evaluation through the coordination session (the coordinating session, 2026-10-25 ~15:00Z). The files listed in
SHA256SUMS_T_v1 are part of this pre-registration. The T2 sample is drawn from T1's unit list by the frozen tool and
seed below, and it is frozen in `T/ADDENDUM_T2_sample.md` (with its sha256) before any T2 run. Later changes go to
DEVIATIONS.md, which is append-only; this file is never edited.

## Target

- Apache Thrift, `github.com/apache/thrift` at `f0eb8b84eb5654a949dda7c8ae444a11ca63e632` (2026-10-24), as cloned by
  veriforch at `~/veriforch/targets/thrift`.
- Tool pins are recorded when each part starts: cirlean (C and C++), JimpleLean (Java), veriforch's Rust adapter with
  its Charon and Aeneas versions (Rust), StrictTS (TypeScript), Lean v4.35.0, clang upstream-4955d32b, Soot 4.7.1,
  JDK 17, and veriforch as a frozen copy with a SHA256 manifest. No re-pin during a run. Crash fixes only, each one
  recorded, and the affected units are re-run.

## Languages and components (frozen rules: `T/tools/thrift_paths.py`)

- Language by file extension: C++ (.cpp .cc .cxx .hpp .hh .tcc, and .h outside lib/c_glib), C (.c, and .h under
  lib/c_glib), Java (.java), Rust (.rs), TS (.ts, not .d.ts). JavaScript and every other language (Go, PHP, Ruby,
  Python, Perl, C#, D, Dart, Erlang, Haxe, Lua, OCaml, Smalltalk, Swift, Kotlin, Delphi, ...) are out of scope.
- Component, first matching rule on the repository path: `compiler/...` is compiler; a directory named `protocol`,
  `transport`, `server` or `concurrency` gives protocol, transport or server; otherwise the file name (protocol:
  contains Protocol; transport: Transport or Socket; server: Server, Thread or Concurrency); otherwise other.
  "server" stands for server/concurrency.
- A library source file of a supported language is a supported-language file under lib/cpp, lib/c_glib, lib/java,
  lib/rs, lib/ts or lib/nodets, outside any directory named test(s), tutorial, example(s) or benchmark(s).

## T1: whole-codebase coverage scan (no model calls)

- Denominator: every source file of the repository at the pin, by language and component, as physical lines; for the
  supported languages also as units (function and method definitions with a body, as each front end enumerates them:
  cirlean over the CMake build's compile commands for C and C++, Soot over the built jars for Java, veriforch's Rust
  adapter over the thrift crate, StrictTS for TypeScript).
- Out of scope, reported as such and kept in the denominator: the other languages (about 43% of the code by the
  user's estimate) and untyped JavaScript (about 21k lines by the same estimate). T1 measures both.
- In scope: a unit whose call-graph closure uses only constructs that its semantics models (D's definition: no gap,
  no unmodelled library call, emitted by the front end).
- Report: the in-scope rate per language and component (units), with Wilson 95% intervals where it is a proportion
  over units; the blocker families ranked by the number of units whose closure carries them (D2's families and
  `blocker_freq.py` rules); and the share of the codebase, in lines, that is out of scope by language.
- Output that T2 needs: the unit list of the supported languages as a TSV with the columns `language`, `unit` (a
  unique key) and `path` (the source file, relative to the repository root), with every unit of the frame, in scope
  or not.

## T2: stratified random sample

- Frame: every unit of the supported languages in T1's unit list, in scope or not (a blocked unit counts as blocked).
- Strata: language (C++, C, Java, Rust, TS) x component (protocol, transport, server, compiler, other).
- Size and allocation (`T/tools/draw_t2.py`, defaults N = 1000, MIN = 20): each stratum first gets min(N_s, 20) units,
  a census where N_s <= 20. The rest of N is shared out in proportion to N_s - min(N_s, 20) by the largest-remainder
  method, never above N_s. If the frame has fewer than N units, all are drawn.
- Draw: seed `fv-paper-prereg-T-2026-10-25`, per stratum as in the tool; the processing order is one seeded
  permutation of the whole sample, so that every prefix is a random subsample.
- Per unit, in processing order:
  1. `vo verify --only <unit and its call-graph closure> --attempts 3 --check-timeout 600 --budget 0.25`, with a
     10-minute wall per unit (compute);
  2. the counterexample step where the bridge has one, within the unit's budget;
  3. the kernel replay of every claimed theorem with `lake env leanchecker <module>` in the package that built it.
  A callee proved for an earlier unit is reused at no cost.
- Outcomes: the R6 mapping of PREREG_D_v2, unchanged, with the readings recorded in DEVIATIONS.md for D (a
  negative-cache "stuck" is a timeout; a wall kill is a timeout whatever status was recorded; a tool crash is an
  infrastructure error until its crash fix and re-run): proved mechanical, proved model-stated, native (apart),
  conditional, partial, refuted, blocked (with the gap name), timeout, infrastructure error.
- Budget and stop rule: T2 model spend at most $500 (veriforch's usage logs). Processing stops at the current position
  at the earlier of the budget and Tue 2026-10-27 03:00Z. Unattempted units are reported and left out of the
  denominators; because the order is random, the attempted prefix is still a random sample of every stratum.
- Analysis:
  - per stratum: counts and proportions of every outcome, with Wilson 95% intervals;
  - per language and overall: the stratified estimate sum_s (N_s / N_frame) p_s over the strata with attempted units,
    with a 95% interval from its variance sum_s (N_s / N_frame)^2 p_s (1 - p_s) / n_s (normal approximation), and the
    unweighted proportions next to it;
  - cost per unit (model $ and core-seconds: median, interquartile range, mean, total); gap names with frequencies;
  - no pooling with D or D2, and nothing excluded after the fact.

## T3: CI verdicts over Thrift's history

- Commits (frozen list `T/t3_commits.tsv`, 150 commits, made by `T/tools/select_t3.py` at the pin, read-only):
  - rule (a): every non-merge commit in the 365 days before the pin that changes a library source file of a supported
    language (143 commits that only rule (a) selects);
  - rule (b): every non-merge commit whose message names a THRIFT ticket that the repository's own
    doc/thrift-threat-model.md or CHANGES.md associates with a CVE or calls CVE-class (THRIFT-4506, -5716, -3821,
    -5812, -5469, -5221, -5255) and that changes such a file (7 commits: THRIFT-3821 x2, -4506 x2, -5221, -5255,
    -5716). No commit message in the history names a CVE number directly.
  - Processing order: the rule-(b) commits oldest first, then the rule-(a) commits newest first.
- Procedure per commit c with parent p (as C1 of PREREG_C_v2): `vo ci <lib target of each touched supported language>
  --base p --head c --attempts 0 --budget B --check-timeout 600`, B = $0.50 x the number of changed functions. The
  verdict obligations are stated and attempted without the model; the model only proposes distinguishing inputs for
  functions with pointer or reference parameters, two per function. A commit whose parent or itself does not build
  with the pinned flags is blocked: build, with the error.
- Outcomes: PREREG_C_v2's definitions, per changed function (equivalent; changed_only_where_old_unsafe;
  behaviour_changed with a distinguishing input confirmed on the semantics; unknown with the reason) and per commit
  (certified conservative, certified equivalent, behaviour change shown, partly certified, unknown, blocked: build).
  Every claimed verdict theorem: axioms printed and kernel replay.
- Budget and stop rule: T3 model spend at most $300; processing stops at the earlier of the budget and Tue
  2026-10-27 03:00Z; unattempted commits are reported.
- Analysis: a census of the attempted commits: counts per language and in total, every behaviour_changed witness listed
  and re-run by the evidence owner (including whether it needs an input the library's callers never build), and the
  reason for every unknown. No intervals.

## T4: cross-language consistency of the wire protocol (equiv-lean)

- One Lean specification of the encodings: unsigned varint (7-bit groups, least significant first, high bit = more);
  zigzag for i16/i32/i64; the compact field header (one byte `delta << 4 | type` when 1 <= id - last <= 15, else the
  type byte followed by the zigzag varint of the i16 id); the compact list/set header (`size << 4 | elemType` when
  size < 15, else `0xF0 | elemType` followed by the varint size); the compact string/binary length prefix (varint32
  length, then the bytes); the binary protocol's big-endian i16/i32/i64 and its i32 length prefix.
- Functions, in C++ (lib/cpp TCompactProtocolT, TBinaryProtocolT), Java (lib/java TCompactProtocol, TBinaryProtocol)
  and Rust (lib/rs protocol/compact.rs, protocol/binary.rs), each with the library functions it calls:
  - compact: varint32 and varint64 write and read; zigzag i32 and i64 in both directions; the field header write
    (C++/Java writeFieldBeginInternal, Rust write_field_header) and read (readFieldBegin, read_field_begin); the
    list/set header write (writeCollectionBegin, write_list_set_begin) and read (readListBegin/readSetBegin,
    read_list_set_begin); the string/binary length prefix write and read;
  - binary: writeI16/I32/I64 and the readers; the i32 length prefix of strings and binaries, write and read.
- Statements, per function pair and language:
  - (E) for every value of the function's domain (integers of the declared width; for headers, every element type,
    every size >= 0 and every previous field id), the encoder appends exactly spec(x) to the transport;
  - (D) for every x and every byte sequence rest, the decoder on a transport holding spec(x) ++ rest returns x and
    leaves exactly rest;
  - (M) on malformed input, namely overlong varints (more than 5 bytes for varint32, 10 for varint64), varints whose
    value exceeds the type, negative sizes, field ids and deltas outside the encodable ranges, and truncated input, the
    behaviour of each language is stated as a theorem (the error it raises or the value it returns). Behaviour that
    differs between the languages is reported as a cross-language discrepancy, with the byte sequence, run on each
    language's semantics.
- Transports are modelled per language as abstract byte sinks and sources with stated contracts (a write appends its
  bytes; a read returns the next bytes or reports end of input). The theorems are conditional on these contracts,
  which are written once per language and listed with the results; this is accepted for T4.
- Outcomes, per function pair and language: proved (E and D, and M stated), discrepancy exhibited (with the input),
  or not finished by the freeze. Every function listed above is reported; none is dropped after the fact.
- Budget: at most $1.5k (equiv-lean tracks it with its other work). Start after equiv-lean's 751764f freeze build.

## Known before the run (disclosure)

- T1 is being run by veriforch while this file is frozen (no model calls). The language shares quoted above come from
  the user's message, not from T1.
- veriforch's Rust adapter is new (the user's 10-25 item, cap $1k). Thrift's TypeScript consists of test files and a
  type declaration file (9 .ts files at the pin), so the TS strata are expected to be small censuses.
- The T3 list was computed before this file was frozen and is part of it.
