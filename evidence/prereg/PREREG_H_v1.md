# Pre-registration H: Theorem's proved fuzz harnesses at source level (UB sweep and harness proofs)

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before any H run. The user asked for this
through the coordination session (the coordinating session, 2026-10-25 ~16:00Z); veriforch (the orchestrator session) runs it. The selection table and the
pins go into `H/ADDENDUM_H_selection.md` before the first H run. Later changes go to DEVIATIONS.md, which is
append-only; this file is never edited.

## Population and selection (rules fixed now)

- Population: the 60 entry points in the "What is proved" table of Theorem's README at
  github.com/theorem-labs/oss-verify-proofs commit 98e995d4daced70a0a4aa2c810854b88720735f1 (release 2026.10.0;
  README sha256 58e191365e6993e596e88f9b832136bb106077935dd66088c6c5afca874706e2).
- C entry point: every harness source file is C (.c) and, by Theorem's build record, the binary links only objects
  compiled from C.
- Size: the physical lines of the .c and .h files of the upstream repository at the commit Theorem's build record
  gives for the entry point, without the harness files and without directories named test, tests, fuzz, fuzzing,
  example, examples, doc, docs, bench, benchmark, benchmarks or contrib.
- Selected: the C entry points of size at most 20,000 lines. If more than 12 qualify, the 12 smallest (ties by name).
  cJSON's cjson_read_fuzzer is among them if it qualifies. Processing order: ascending size.
- veriforch computes the table (entry point, harness files, languages of the linked objects, upstream repository and
  commit, size) with a script, and sends the table and the script with their sha256 before any run. The evidence owner
  re-checks the table.

## Part one: source-level UB sweep (no model calls)

- Inputs: the harness's public seed corpus as OSS-Fuzz at commit bd2ce21991a94a362b92fb1bf25f86d5a1a60842 (the commit
  in Theorem's release) packs it, or, if it packs none, the corpus directory of the upstream repository at the
  recorded commit. If there is neither, the entry point is reported as "no public corpus". If a corpus has more than
  500 inputs, 500 are drawn: the inputs sorted by sha256("fv-paper-prereg-H-2026-10-25|<entry point>|<file name>")
  and the first 500 taken.
- Semantics: cirlean at the pin recorded when part one starts; harness and library unmodified, built through
  veriforch's C pipeline.
- Each input runs on the semantics with a 60-second wall. Per input: normal end; undefined behaviour (kind and source
  location); an unsupported construct (named); timeout.
- For each distinct (UB kind, location), one input that reaches it is re-run on native builds with the sanitizer flags
  of Theorem's docs/building.md (ASan, UBSan, ASan+UBSan, on x86-64), and whether a sanitizer reports it is recorded.
- Outcome per entry point: UB found (distinct locations, number of inputs, sanitizer report or silence for each), no UB
  on the corpus, blocked (it does not build or run on the semantics: the gap named), timeouts only, or not attempted.
- Compute at most 60 core-hours for part one.

## Part two: full harness proofs for the three most cJSON-like entry points

- Candidates: the part-one entry points other than cJSON whose harness builds and whose corpus inputs all run on the
  semantics without an unsupported construct. Ranked by |ln(size / size of cJSON)| ascending, ties by name; the first
  three, in that order (all of them if fewer qualify).
- Start: after cJSON's harness result is final (proved, or conditional with its assumptions listed) or at Mon
  2026-10-26 12:00Z, whichever comes first.
- Statement: the statement veriforch proves for cJSON's harness (`LLVMFuzzerTestOneInput_spec`), instantiated for the
  entry point with the same input bound.
- Outcome per entry point: proved (no assumptions), conditional (each assumption listed), refuted (the input, run on
  the semantics), or not finished.
- Every claimed theorem: axioms printed and kernel replay, re-checked by the evidence owner.
- Report: proof size (Lean lines of the closure by role, as for the paper's other proofs), model spend (veriforch's
  usage logs), core-hours (guard logs), wall time, and the marginal cost of each harness after cJSON.

## Budget and stop rule

- H model spend at most $1.5k in total and at most $450 per part-two entry point; part one makes no model calls.
- Compute under the core-hour guard and the machine rules (about 8 one-core jobs at most, 2 at any load, more only
  while the 1-minute load is below 450, none started below 150 GB MemAvailable).
- Processing stops at the earlier of a cap and Tue 2026-10-27 03:00Z. Entry points not attempted are reported.

## Reporting rules

- Theorem's proofs are about compiled binaries and rule out the errors that the sanitizer builds detect, and its
  README says that errors the sanitizers cannot detect are not excluded. A source-level UB found here is reported as
  outside the scope of those proofs, never as a flaw in them.
- Part one is a census of the selected entry points: counts, no intervals.

## Known before the run (disclosure)

- From B: cJSON's `cJSON_SetValuestring` compares unrelated pointers (public issue #919), and Theorem's cJSON harness
  never calls it. veriforch's cJSON harness proof was conditional on two cirlean assumptions (ParseArrayStepSpec,
  ParseObjectStepSpec) at 15:44Z. cirlean is changing type-punned scalar accesses of a different width to undefined
  behaviour (the C maintainer session, today), so the pin recorded at the start decides whether such accesses count as UB.
- The local clone of Theorem's repository (veriforch scratch) holds only proofs/cjson; the build records of the other
  entry points come from the release.
