# Pre-registration M: mutation testing of the four semantics, and of coblean's front end

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before any mutant of a population below is
built or run. The user asked for this through the coordination session (the coordinating session, 2026-10-25 ~16:00Z). The files listed
in SHA256SUMS_M_v1 are part of this pre-registration. Each bridge's frozen inputs (tool, candidate list, order, test
suite) go into `M/ADDENDUM_M_<bridge>.md` before its first population mutant is built. Later changes go to
DEVIATIONS.md, which is append-only; this file is never edited.

## Question

How much of each semantics do its differential tests check? A mutant changes one semantic rule. The question is
whether the tests that compare the semantics with a reference implementation notice.

## Scope: the semantic rules

In scope are the definitions that give meaning to the language's constructs, primitive operations and values (numbers,
strings, data representation, memory). Out of scope: library models, syntax, front ends, lexical tables, proofs and
tactics, and code used only for debugging output.

- C/C++ (cirlean): `CIR/Semantics/{Eval,Basic,Init,Context}.lean`, `CIR/Value.lean`, `CIR/Memory.lean`,
  `CIR/Std/{Float,FloatNaN}.lean`. Library models (`CIR/Model.lean`, `CIR/Std/Models.lean`, `CIR/Std/Ctype.lean`) are
  out.
- COBOL (coblean): `Cobol/Sem/{Exec,Arith,File,Data,Inspect,Unstring,StringInto}.lean` and
  `Cobol/{Codec,Mem,Round,Layout,Edit,Digits,Data}.lean`. `Cobol/Ext/` (models of external routines), `Cobol/IR.lean`,
  `Cobol/Config.lean`, `Cobol/Frontend/`, `Cobol/Logic/` and `Cobol/Target/` are out.
- Java (JimpleLean): `Jimple/Semantics.lean`, `Jimple/Numeric.lean`. `Jimple/Native.lean` (library models), the Unicode
  tables and the decimal-formatting library are out.
- TypeScript (StrictTS): `StrictTS/Core/Sem.lean`, `StrictTS/Lib/Prim.lean`, `StrictTS/Lib/Conv.lean`,
  `StrictTS/Num/F64.lean`, `StrictTS/Str/JSStr.lean`.
- Rust: none. The Rust side uses Aeneas's translation and library, which the paper trusts and does not test here.
- Pins: each owner names its commit in its addendum: the paper's pin or a later commit of the same repository.

## Candidates (each owner's enumeration tool, frozen by sha256)

- A candidate is one textual replacement at one position, inside a definition (def, abbrev, instance, match arm or
  where clause) of an in-scope file. Comments, docstrings, string literals (except under EXC), theorem, lemma and
  example bodies, and bit widths or other type indices are never mutated. The id is `file:line:col:op[:k]`; the list
  is sorted by id.
- Operator families, with fixed maps written in the tool's docstring:
  - ROR, relational: `<`->`≤`, `≤`->`<`, `>`->`≥`, `≥`->`>`, `=`->`≠`, `≠`->`=` (and the Bool forms `==`, `!=`);
  - AOR, arithmetic and bitwise: `+`->`-`, `-`->`+`, `*`->`+`, `/`->`*`, `%`->`/`, `&&&`<->`|||`, `^^^`->`&&&`, and a
    signed operation replaced by its unsigned counterpart;
  - LOG, logical: `&&`<->`||`, `∧`<->`∨`, and a Boolean `!`/`¬` removed;
  - NEG: a unary minus removed;
  - CND: an if/guard condition negated, `if C then` -> `if ¬(C) then`;
  - LIT: an integer literal n -> n + 1 (one candidate per literal; no n - 1);
  - at most three bridge-specific families, each a fixed map declared in the docstring before the list is made, for
    example Java FUN (signExtend<->zeroExtend, sshiftRight->ushiftRight, fcmpl<->fcmpg, dcmpl<->dcmpg) and EXC (a
    thrown exception class -> RuntimeException); TypeScript ARM (a match arm's result replaced by the next arm's) and
    a NaN, -0 or infinity special case's guard replaced by false; C an undefined-behaviour guard replaced by false;
    COBOL a rounding mode replaced by truncation, or a file status or abend code replaced by another.

## Draw (`M/draw_m.py`, frozen here)

1. The owner sends the enumeration tool and the candidate list made at the pinned commit, with their sha256, before
   any population mutant is built.
2. The evidence owner re-runs the tool on the pinned files (the output must be identical) and computes the processing
   order: the candidates sorted by sha256("fv-paper-prereg-M-2026-10-25|<bridge>|<id>"), bridge one of cirlean,
   coblean, jimplelean, strictts, cobolfe. The ordered list and its sha256 go into the addendum.
3. The owner builds and tests the candidates in that order until 30 have been built and tested.

## Build, stillborn candidates, proofs

- A candidate is stillborn when the mutated definition does not elaborate, when the test executable does not build
  for any other reason than a broken proof, or when the build takes more than 60 minutes. Stillborn candidates are
  recorded with the reason and skipped.
- A theorem or lemma that fails only because of the mutation has its proof replaced by `sorry` in the mutant's copy.
  The number of such replacements is recorded per mutant. Definitions are never changed except at the candidate.

## Tests and the kill criterion

- Each bridge's differential suite at its pin, frozen in its addendum (commands, inputs, counts, seeds, sha256) before
  the first population mutant runs:
  - cirlean: the C/C++ differential tests against native execution (the 175-case difftest checked at d9ae8e5, or the
    same suite at the new pin);
  - coblean: every GnuCOBOL differential tester of its validation table at its recorded N and seeds, the front-end
    testers included. The Java/Rust transcription tester does not compare with GnuCOBOL and is not used. If one
    mutant would take more than about 30 minutes, a subset may be declared in the addendum before the first population
    mutant runs, with the cost as the reason;
  - JimpleLean: difftest/src (41 programs) and difftest/regex (3), against the JVM;
  - StrictTS: tests/difftest (180 programs) against Node, and F64Diff and StrDiff at the counts and seeds declared
    in the addendum. tools/validate runs only on survivors, and its result is reported apart ("killed only by the
    extended suite").
- Killed: on some test of the suite the mutant's output (stdout, exit status, or the suite's own comparison) differs
  from the reference, or the mutant crashes, runs out of fuel, or exceeds the test's time limit where the unmutated
  copy passes that test. Survived: every test passes.

## Controls (on the frozen copy, before the first population mutant)

- Baseline: the unmutated copy passes the whole suite.
- A no-op edit (whitespace or a comment in an in-scope file) survives.
- A known-bad edit outside the population (for example in a library model) is killed.

## Equivalent mutants

Survivors stay survivors in the headline. The owner may label a survivor "equivalent" when it is found, with a written
reason or a Lean proof that the mutated and the original definition agree on all inputs. The labels form a separate
column, the evidence owner checks them, and they are reported next to the headline, never subtracted from it.

## Part FE: coblean's front end, before and after added tests

- Population: candidates in `tools/cobolfe/*.py` (coblean's COBOL front end), with the families above adapted to
  Python (ROR, AOR, LOG, NEG, CND on if, elif and while conditions, LIT) plus STMT (a simple statement replaced by
  `pass`). Comments, docstrings, string literals and the code that only formats error messages are not mutated. Tool
  and list are frozen as above. A candidate that fails to import is stillborn.
- Suite: every GnuCOBOL differential tester of the validation table, the front-end testers included, at the recorded
  N and seeds; not the Java/Rust transcription tester. Killed as above; a front-end crash where the original runs is a
  kill.
- Set 1: the first 30 tested candidates in the order of step 2 (bridge `cobolfe`). They run on the suite as it is.
- coblean may then add tests. The extended suite is frozen (commands, inputs, sha256) and sent to the evidence owner
  before set 2 is drawn.
- Set 2 (held out): 30 candidates not attempted for set 1, in the order of `draw_m.py --seed S2 --exclude <the
  candidates attempted for set 1>`, where S2 is a
  secret string whose sha256 is e6e93c3f5a720ac5c188c0f4f7b7a3838497608ef522069357d0fa93c8b8e5c2. The evidence owner
  releases S2 after receiving the extended suite's sha256.
- Runs: set 1 and set 2 each on the old suite and on the extended suite. Headline: set 2's kill rate on the old suite
  against that on the extended suite, the same mutants, which nobody had seen when the tests were written. Set 1's
  figures are reported as well, labelled as not independent of the added tests.
- The README's earlier figure (one planted `-`->`+` bug that failed 6 of 30 programs) is about one mutant; it is not
  this measure, and the paper does not pool the two.

## Budget and stop rule

- Compute only; no model calls. Every run is under the core-hour guard, with at most 20 core-hours per bridge and 20
  for part FE. The machine rules hold: about 8 one-core jobs at most, 2 at any load, more only while the 1-minute load
  is below 450, none started below 150 GB MemAvailable.
- Processing stops at Tue 2026-10-27 03:00Z. Unattempted candidates are reported. Because the order is random, the
  attempted prefix is a random sample of the population.

## Analysis

- Per bridge: mutants built n, killed k, survived n - k, the kill rate k/n with a Wilson 95% interval, stillborn
  candidates by reason, counts per family, every survivor listed (id, family, original and replacement, equivalence
  label if any), core-seconds per mutant (median and total). No pooling across bridges in the headline; a total may be
  shown as a description.
- Part FE: the two kill rates of set 2 with Wilson intervals, the mutants killed by the extended suite only, and set
  1's figures with their label.

## Known before the run (disclosure)

- JimpleLean (the Java maintainer session) built its harness and a draft list before this file: 540 candidates (enumerate_sites_v1.py
  c749ce85..., population_draft_v1.tsv 13501910...), corpus_v1 of 44 programs, and a control self-test (baseline 44/44,
  a Native.lean mutant killed, a no-op edit survived). No population mutant was built or run. The draft includes
  n -> n - 1 literal candidates, which this file does not use, so the tool changes before its list is frozen.
- StrictTS (the TypeScript maintainer session) sent its file list and a cost estimate (about 8-10 core-hours for 30 mutants). coblean (the COBOL maintainer session) asked
  for these definitions before running anything. cirlean (the C maintainer session) has not built anything.
