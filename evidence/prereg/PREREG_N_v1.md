# Pre-registration N: coblean on the NIST COBOL85 test suite (batch-relevant modules)

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before coblean runs any NIST program. The
user asked for this through the coordination session (the coordinating session, 2026-10-25 ~16:00Z); coblean (the COBOL maintainer session) runs it. coblean's
frozen inputs go into `N/ADDENDUM_N_inputs.md` before its first NIST run. Later changes go to DEVIATIONS.md, which is
append-only; this file is never edited.

## Suite and reference

- The NIST COBOL85 suite as GnuCOBOL distributes it (newcob.val, CCVS85), split into programs, copybooks and data
  files by coblean's `tools/nist/extract.py` with GnuCOBOL's EXEC85 configuration, as EXEC85 does.
- Reference: GnuCOBOL 3.2.0 (the version of the paper's validation runs), each program compiled and run with the flags
  of GnuCOBOL's own cobol85 test harness for its module.

## Modules (rule fixed before any run)

A module is batch-relevant when its feature area occurs in at least one program of CardDemo's batch layer (the CB*
programs of `app/cbl` in the CardDemo checkout used for the paper, ~/coblean_corpus/carddemo). The evidence owner's
grep of those 12 programs (comment lines skipped) finds indexed files in 11, sequential files in 6 (by an explicit
ORGANIZATION clause), COPY in 11, CALL in 11 (CEE3ABD, COBDATFT, CBSTM03B), intrinsic functions in 4 (CURRENT-DATE in
3, MOD in 1), and no SORT, MERGE, relative files, report writer, debugging, segmentation or communication. In scope, in this processing order: NC (nucleus), SQ (sequential I-O), IX (indexed
I-O), SM (source text manipulation), IC (inter-program communication), IF (intrinsic functions). Out of scope: RL, ST,
RW, CM, DB, SG, OB. Every program of an in-scope module is run; none is dropped after the fact.

## Runs

- Within a module, programs run in newcob.val's order, with one file directory per module that persists from program
  to program, as EXEC85 does, separately for GnuCOBOL and for coblean.
- coblean: its front end on the program, then its semantics (cobolrun) at the pinned commit, with a 10-minute wall
  per program on one core.
- A frozen report parser (coblean writes it; sha256 in the addendum) reads each program's report file into its
  verdict vector: the sequence of (test name, verdict) with verdict PASS, FAIL, DELETED or INSPECT. Parser check before
  any coblean run: on GnuCOBOL's reports, the parser's per-module totals equal GnuCOBOL's own count of those reports.

## Outcomes per program

- pass: coblean's front end accepts the program, the semantics runs to the end (or to the same abend as GnuCOBOL),
  and the verdict vector equals GnuCOBOL's.
- fail: coblean runs to the end or abends, and the verdict vector differs from GnuCOBOL's, or exactly one of the two
  abends.
- unsupported: the front end rejects the program, or the semantics stops with its "unsupported" outcome (the
  construct is named).
- undefined: the semantics stops with its "undefined" outcome (named); reported apart, since the suite tests defined
  behaviour.
- timeout: the fuel or the 10-minute wall runs out.
- no reference: GnuCOBOL does not compile or run the program with its harness flags. Listed, and left out of the
  denominators.
- A program whose input files come from an earlier program that did not pass in coblean keeps its outcome and gets
  the flag "after a non-passing producer".

## Analysis

- Per module and in total: the number of programs per outcome. This is a census of the in-scope modules: counts, no
  intervals.
- Per test: for the programs that ran to the end in coblean, the number of verdict-vector entries equal to
  GnuCOBOL's, over GnuCOBOL's entries.
- NIST's own grading (PASS, FAIL, DELETED, INSPECT totals) for both systems, per module.
- Every fail with its first differing test, every unsupported or undefined outcome with its construct, and the
  constructs ranked by the number of programs they block.

## Inputs frozen before coblean's first NIST run (N/ADDENDUM_N_inputs.md)

newcob.val and the EXEC85 configuration (source, sha256); extract.py and its manifest of programs per module (sha256);
the GnuCOBOL binary, version and flags per module; coblean's pinned commit; the runner and the report parser
(sha256); the parser check. GnuCOBOL's reference runs may happen before the addendum; they are the reference, not the
measured system.

## Budget and stop rule

- Model spend at most $200 (triage only; the runs need no model). Compute under the core-hour guard and the machine
  rules (about 8 one-core jobs at most, 2 at any load, more only while the 1-minute load is below 450, none started
  below 150 GB MemAvailable).
- Processing stops at Tue 2026-10-27 03:00Z. Programs not attempted are listed, module by module.

## Known before the run (disclosure)

- coblean wrote `tools/nist/extract.py` before this file. It proposed the modules NC, SM, IC, SQ and IX, and left out
  IF because it models no intrinsic function; the rule above includes IF because CardDemo's batch programs use
  CURRENT-DATE and MOD. coblean asked for these definitions before running any NIST program.
