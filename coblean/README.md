# coblean: a formal COBOL IR in Lean 4 for proving rewrites equivalent

`coblean` is a Lean 4 specification of a normalized COBOL intermediate representation and
its semantics, plus proof automation for showing that a COBOL program and a Java or Rust
rewrite of it compute the same results, bit for bit, for all valid inputs.

The IR is deliberately *not* lowered to a C-like runtime. It keeps COBOL's own concepts:
- hierarchical working storage as bytes, with `REDEFINES` overlays and `OCCURS` tables;
- `PICTURE` decimal fixed-point values with exact rounding and truncation rules (DISPLAY, COMP-3, COMP, COMP-5);
- `MOVE` padding, justification and editing;
- `PERFORM … THRU` with IBM's return-slot semantics.

Values are scaled integers (`value = v · 10^-scale`). The same primitives model Java's
`BigDecimal` and `int`/`long`, and Rust's `i64`/`i128`, so most of an equivalence proof is
definitional unfolding. `omega`, `grind`, `bv_decide`, interval arithmetic and congruence
closure do the rest.

```
COBOL source + copybooks
   │  tools/cobolfe (parser, COPY and REPLACE, name resolution)
   ▼
surface IR (JSON)  ── extraction contract: Cobol/Frontend/Surface.lean
   │  cobol_program P from "p.json"        (layout, offsets, encodings: in Lean)
   ▼
core IR  P : Cobol.Program  ── semantics: Cobol/Sem/*  (byte storage, scaled integers)
   │
   │   cobol_equiv / cobol_bv              Java / Rust transcription over
   ▼                                        Cobol/Target/{Java,Rust,Bits}.lean
theorem: obs (P.run …) = obs (javaMethod …)
```

Toolchain: Lean `v4.35.0` (core and Std only, no Mathlib). About 6,200 lines of Lean in the library,
430 in the examples.

## Contents

| Path | What |
|---|---|
| `Cobol/Round.lean` | scaled integers; `divRound` for all 8 COBOL 2014 rounding modes (= Java `RoundingMode`, rust_decimal `RoundingStrategy`); monotonicity |
| `Cobol/Config.lean`, `Data.lean` | compiler options (`TRUNC`, codepage, sign conventions, endianness), item formats (`NumFmt`, `FieldKind`) |
| `Cobol/Codec.lean` | zoned (EBCDIC / ASCII / overpunch / separate sign), packed (COMP-3), binary (COMP/COMP-5) codecs, with round-trip and range theorems |
| `Cobol/Mem.lean` | storage as a byte array; field read/write lemmas (same / disjoint / within / overlapping) |
| `Cobol/Layout.lean` | data division layout: levels, `REDEFINES`, `OCCURS`, `SYNC`, `VALUE` |
| `Cobol/IR.lean` | the core IR: data references, expressions, conditions, statements, programs, state |
| `Cobol/Edit.lean` | numeric editing (`Z`, `*`, `$`, `+`, `-`, `CR`, `DB`, `B`, `0`, `/`, `,`, `.`, `BLANK WHEN ZERO`; the characters of `DECIMAL-POINT IS COMMA` and `CURRENCY SIGN`) |
| `Cobol/Sem/Data.lean` | references, subscripts, reference modification, storing, `MOVE` |
| `Cobol/Sem/Arith.lean` | exact expression evaluation, intermediate scales, IBM's 30-digit intermediate results, `ROUNDED`, `ON SIZE ERROR`, conditions |
| `Cobol/Sem/File.lean` | files: `OPEN`/`READ`/`WRITE`/`REWRITE`/`DELETE`/`CLOSE` on sequential and indexed (VSAM KSDS) files, IBM `FILE STATUS` codes |
| `Cobol/Sem/Exec.lean` | statements and control flow: `PERFORM` (all forms), `GO TO`, `ALTER` (lowered), sections, `EXIT`, loops, files, `CALL` (environment or linked), `SET ADDRESS OF`, clock, abend |
| `Cobol/Spec.lean` | outcome predicates (`Program.EndsNormally`) |
| `Cobol/Frontend/*` | the extraction contract (surface IR), the resolver (surface → core), the JSON loader and the `cobol_program` command |
| `Cobol/Target/Java.lean`, `Rust.lean`, `Bits.lean`, `Codepage.lean` | target-language models (`BigDecimal`, `Math.*Exact`, `i64`/`i128` checked arithmetic, `ByteBuffer`, CP037) |
| `Cobol/Logic/*` | proof automation: symbolic execution, state merging, interval bounds, loop induction, `PERFORM` summaries (`Summary.lean`), equivalence tactics, fuel monotonicity (`FuelMono.lean`), loops that stop early (`LoopExit.lean`) |
| `Examples/`, `Examples.lean` | proved equivalences (below) |
| `tools/cobolfe/` | the COBOL front end: COBOL source + copybooks → surface IR |
| `tools/records.py` | record images ↔ field values from a surface-IR program (for test data and replay through `cobolrun --inputs`) |
| `examples/` | COBOL sources, Java/Rust rewrites, hand-written IR builders, GnuCOBOL validation scripts; `examples/carddemo/`: front-end IRs of AWS CardDemo batch programs |
| `tools/difftest/` | differential testing of the semantics against GnuCOBOL |
| `tools/targettest/` | differential testing of the Lean transcriptions against the real Java/Rust code |
| `bench/` | scaling benchmark generators |
| `CobolRun.lean` | `cobolrun`: the semantics as an executable reference interpreter |

## Quick start

```sh
python3 -I tools/cobolfe/cobolfe.py PROG.cbl -I copybooks/ -o prog.json   # extract (IBM profile)
scripts/lrun.sh lake build                 # library
scripts/lrun.sh lake build Examples        # check every proved theorem (≈ 25 s)
scripts/lrun.sh lake build cobolrun        # reference interpreter
scripts/lean1.sh Examples/AcctInt.lean     # check one file (prints the axioms of its theorems)
scripts/check_all.sh 20                    # everything, plus 20 random cases per validation
```

`cobolfe.py` options: `--profile ibm|gnucobol` (character set and sign conventions),
`--trunc std|opt|bin`, `--main`/`--sub`, `--report` (coverage report), `--switch NAME=ON|OFF`
(a switch's state at the start of the run; without it the switch is off, or with `--profile
gnucobol` it takes `COB_SWITCH_n` from the environment, as GnuCOBOL does). The front end drops
nothing that can change what a program does. A statement or phrase it cannot express becomes
an `unsupported` statement, which faults when it is reached. A construct outside the
statements that the model does not cover (`BLANK WHEN ZERO` on a signed number,
`USE FOR DEBUGGING`, sort files, …; the list is under *Model and limitations*) makes the
whole program unsupported: its first statement faults, so no run or proof can depend on it.
Both kinds are listed on stderr.
`cobolrun prog.json --inputs files.json --clock 2025102314301234-0500` runs an extracted
program on concrete files; `--absent 1,3` makes the `OPTIONAL` files 1 and 3 absent when the
run starts; `--sysin records.json` gives the records of the system input device that `ACCEPT`
reads (a JSON list of records, each a list of bytes in the program's character set, as in
`--inputs`; without it the run has no system input device, and an `ACCEPT` from it faults).

The validation scripts write their programs and data to `out/` directories next to them.

`scripts/lrun.sh` / `scripts/lean1.sh` run Lean with 1 thread, an address-space cap, `nice`, a
timeout, and a project-local `TMPDIR`. `lean1.sh` also passes `-DElab.async=false`, because
async elaboration spawns about 16 threads.

## The examples

### ACCTINT ≡ Java (`Examples/AcctInt.lean`)

`examples/acctint/ACCTINT.cob` (with copybook `ACCTREC.cpy`) accrues daily interest on an
account record:
- a COMP-3 balance with a `REDEFINES` byte view, tested against LOW-VALUES;
- a type check, then `COMPUTE … ROUNDED` with IBM's intermediate-precision rule;
- `ON SIZE ERROR` in a `COMPUTE` and an `ADD`;
- level-88 status values;
- `PERFORM 1000-CALC THRU 1000-EXIT` with `GO TO 1000-EXIT`.

`examples/acctint/AcctInt.java` is the rewrite, using `BigDecimal` with `HALF_UP`.

```lean
cobol_program AcctInt from "../examples/acctint/acctint.ir.json"

open AcctInt in
theorem acctint_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int) (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) :
    cobolObs (AcctInt.run {} 20 (AcctInt.initState m)) =
      javaObs (AcctIntJava.accrue (Codepage.cp037Char ty) (some (.valueOf bal 2))
        (.valueOf rate 5) days) := by
  cobol_ranges
  have hz : ¬ m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  have := daily_rate_eq rate
  cobol_equiv [cobolObs, javaObs, hm, hty, hbal, hrate, hdays, hz,
    AcctIntJava.accrue, AcctIntJava.ZERO2]
```

The only proof step that needs thought is `daily_rate_eq`. COBOL computes `RATE / 365`
truncated to 9 places and then rounds to 8. Java rounds the exact quotient once. The lemma
states that these agree; `cobol_arith` proves it in one line. Everything else is automatic:
- the input ranges (`cobol_ranges`);
- that a valid packed field is never LOW-VALUES (`hz`, one line);
- every size-error test, both rounding pipelines, and the codepage of the status byte.

A second theorem covers the LOW-VALUES case, where Java receives `null`. Checking the file
takes about 3 s.

### ACCTINT ≡ Rust (`Examples/AcctIntRust.lean`)

`examples/acctint/acctint.rs` is a scaled-integer rewrite:
- `i64` cents and `i128` intermediates;
- a hand-written `div_half_up`;
- debug-build overflow panics.

The proof has the same shape. One library lemma, `Rust.divRound_halfUp_idiom`, folds the
Rust rounding idiom into `divRound`. The theorem also shows that the Rust code never panics
on a valid record: every `i128` overflow check is decided from the input ranges by interval
arithmetic.

### BINCNT ≡ Java `short`/`int`, bit for bit (`Examples/Binary.lean`)

`examples/binary/BINCNT.cob` does three things:
- adds 1 to a `PIC S9(4) COMP-5` counter, which wraps at 32767;
- adds three times the counter to a `PIC S9(9) COMP-5` total, with the counter sign-extended;
- copies the total's high half through a `REDEFINES` byte view.

`BinCnt.java` does the same with `ByteBuffer`, `short` and `int`. The proof is one call,
`cobol_bv [hm, hc, ht, BinCntJava.update]`. It runs symbolic execution, restates the stored
bytes as `BitVec` terms (`Cobol/Target/Bits.lean`), and calls `bv_decide`. The theorem
covers all 2⁴⁸ input contents, overflow included.

A wrong rewrite that keeps the counter in an `int` is refuted. `bv_decide` prints the
counterexample (counter bytes `7F FF`), and `decide +kernel` proves the difference on it.

### RECSUM: a batch program over a file of any length ≡ a Java loop (`Examples/RecSum.lean`)

`examples/recsum/RECSUM.cob` reads amount records until end of file
(`PERFORM 2000-PROCESS UNTIL EOF`), keeps a running total, and writes one output record per
input record. `RecSum.java` is a `for` loop with a `BigDecimal` total.

The theorem holds for every input file of up to 9999 records. Beyond that, `WS-TOTAL
PIC S9(9)V99` may overflow: COBOL truncates silently and `BigDecimal` does not, so the bound
is part of the equivalence.

The loop cannot be unrolled. Symbolic execution leaves loops with symbolic fuel folded and
stops in front of them. `cobol_loop Inv recs` then replaces the loop by its result, by
induction over the records (`loopUntil_list` in `Cobol/Logic/Loops.lean`).

The human input is the loop invariant `RecSumInv`. It relates the storage (current record,
end-of-file flag, total, count) and the output file to the Java state after the records
already processed. The four obligations are each proved by symbolic execution and
`cobol_grind`:
- the invariant holds before the loop;
- the input fits the fuel;
- the loop condition holds exactly at end of file;
- one iteration preserves the invariant.

Checking the file takes about 3.5 s.

Fuel only bounds the run. `Program.run_mono` (`Cobol/Logic/FuelMono.lean`, every statement form,
paragraph transitions and `GO TO`) shows that a run ending with any signal but `outOfFuel` ends
the same way, in the same state, with any larger fuel. A theorem stated for fuel `n + c`
therefore holds for every sufficient fuel; `tests/FuelMonoUse.lean` restates `cbcus01c_lists`
that way in five lines.

### Real legacy code: AWS CardDemo (`Examples/Cbact0*.lean`, `Examples/Cbcus01c.lean`, `Examples/Cbtrn0*.lean`)

[AWS CardDemo](https://github.com/aws-samples/aws-mainframe-modernization-carddemo) (Apache-2.0)
is a mainframe credit-card application written for migration tools. Its batch programs go
through the front end unchanged, with their real copybooks. Of the 12 `CB*` programs, 10 map to
the IR with no `unsupported` statement. They include CBACT01C, with its variable-length records
and its call of the assembler routine COBDATFT (modelled from its source), and CBSTM03A, which
reads z/OS control blocks through pointers, uses `ALTER`, and calls CBSTM03B (the front end
links the two IRs). CBEXPORT and CBIMPORT declare their `RECORD KEY` in WORKING-STORAGE, which
IBM does not allow, and the resolver rejects them.

They run in `cobolrun` on CardDemo's own sample data (`app/data/EBCDIC`): CBTRN02C posts the
300 sample transactions, CBTRN03C reports on the result, CBSTM03A and CBSTM03B print the account
statements from it (all 7294 records equal GnuCOBOL's), CBACT04C computes interest with five
indexed and sequential files, keyed reads and `REWRITE`. `examples/carddemo/README.md` has the
commands, the abstractions (clock, abend, COBDATFT, uninitialized storage, static `CALL`, z/OS
control blocks), the behaviors seen on the sample data, and coverage over all 44 CardDemo
programs.

Functional theorems about these unmodified programs, for every input file and every initial
storage:
- `cbact02c_lists` (CBACT02C, card file listing): when the file opens, the program ends with
  `GOBACK`. Its `DISPLAY` output is the start message, every record in file order, and the end
  message. The proof takes about 50 lines: a loop invariant (14 lines) and four obligations
  closed by `cobol_sym`. It checks in 9 s.
- `cbact03c_lists`, `cbcus01c_lists` (cross-reference and customer listings): the same proof
  with the program-specific constants substituted (name, storage size, record length,
  messages). Both programs display every record **twice**: `GET-NEXT` displays it after the
  `READ`, and the main loop displays it again. The specs state this.
- `cbact02c_lists'` (`Examples/Cbact02cSum.lean`): the same theorem, with the loop step using a
  summary of `1000-CARDFILE-GET-NEXT` instead of executing the paragraph (see *Summaries*).

Proof effort. Program size is non-comment COBOL lines plus copybooks; proof lines are the
theorem statement and its proof, without blank lines. The CBACT04C proofs are a fixed recipe:
symbolic execution, `rw [loopUntil_succ_before]` once per loop iteration, and a final `simp`.

| Program | COBOL + copybooks | Spec + proof | Human input |
|---|---|---|---|
| CBACT02C | 129 + 8 | ≈ 70 lines (invariant 12) | loop invariant, messages |
| CBACT03C, CBCUS01C | 130 + 5, 130 + 20 | the CBACT02C proof, constants substituted | none beyond the spec change (records shown twice) |
| CBACT04C, one account | 552 + 48 | statement ≈ 25 (input shapes), proof 19 | input shapes |
| CBACT04C, two accounts | 552 + 48 | statement ≈ 40, proof 27 | input shapes, the expected rewritten record |
| CBACT04C, one account, any number of records | 552 + 48 | invariant 21, statement 26, proof 78 | loop invariant, input shapes |
| CBACT04C, any input (`cbact04c_all`) | 552 + 48 | invariant 31, statement 23, proof 213, input model and list lemmas 117 | loop invariant, input model, expected rewritten records |
| CBACT04C, every event (`cbact04c_events`) | 552 + 48 | model 32 and its lemmas 83, invariant 33, statement 22, proof 218 (the `cbact04c_all` proof, events added) | the event model |
| CBACT04C, every input (`cbact04c_every`) | 552 + 48 | 783 lines on top of `cbact04c_events`: model `model4x` (lookups by key, the `DEFAULT` retry, the abends) and its lemmas, invariant and exit state, statement, proof (21 cases) | the failure paths and the `DEFAULT` retry |
| CBTRN01C, any input (`cbtrn01c_verifies`) | 415 + 77 | invariant 15, statement 9, proof 87, input model and lemmas 41, 13 messages | loop invariant, input model, expected display output |
| CBTRN02C, any input (`cbtrn02c_posts`) | 619 + 56 | model 123, lemmas 255 (validity, counts, keyed files, record fields), invariant 22, statement 17, proof 198 | the posting model, loop invariant, record structures |
| CBACT01C, any input (`cbact01c_extracts`) | 358 + 50 | model 58, invariant 13, statement 6, proof 74, field and COBDATFT lemmas | the extract model; COBDATFT's model (from its asm source) |
| CBTRN03C, any input in its domain (`cbtrn03c_report`) | 545 + 87 | model 123 (report lines, `report3`, `eofEvents`), lemmas 219 (edited amounts, record fields, model counts and bounds), invariant 37, statement 27, proof 184 | the report model, loop invariant, record structures, the domain |
| CBTRN02C, any transaction ids (`cbtrn02c_any`) | 619 + 56 | 516 lines on top of `cbtrn02c_posts`: stop model `modelX` and its lemmas, invariant and exit state, statement, proof | the duplicate-key stop |
| CBTRN03C, a date out of range (`cbtrn03c_stops`) | 545 + 87 | 250 lines on top of `cbtrn03c_report`: invariant without the end of file, exit state, statement 30, proof (the five record cases reused, the exit case new) | the stop through `NEXT SENTENCE` |
| CBTRN03C, every input with no blank card number (`cbtrn03c_any`) | 545 + 87 | 564 lines on top of `cbtrn03c_stops`: outcome model `report3x`/`result3` and its lemmas, invariant and exit state, statement, proof (four end-of-file, five record and eight abend cases) | the date stop and the lookup abends |
| CBTRN03C, every input (`cbtrn03c_every`) | 545 + 87 | 594 lines on top of `cbtrn03c_any`: the fold from `init3 x0` and its lemmas, `result3_every`, invariant, statement, proof (three new leaves for a blank first card) | the initial account id as a parameter |

Together, the eight programs with all-input theorems have 3 229 COBOL lines with their copybooks
(2 878 without). Their proof files have 5 758 non-comment Lean lines, about 1.8 per COBOL line.
This counts every file the strongest theorems import, with the models, lemmas, invariants and the
intermediate theorems (for CBACT04C, CBTRN02C and CBTRN03C the strongest are `cbact04c_every`,
`cbtrn02c_any` and `cbtrn03c_every`, which drop most domain assumptions).

CBACT04C has two defects that a rewrite must either reproduce or knowingly fix:
- the last account's interest is never posted. The `ELSE PERFORM 1050-UPDATE-ACCOUNT` branch is
  dead, because the loop test exits first, so the last account is never rewritten. This defect
  was reported in
  [CardDemo issue #64](https://github.com/aws-samples/aws-mainframe-modernization-carddemo/issues/64)
  (2026-10-03); what is added here are theorems that state it for all inputs;
- the transaction records' `TRAN-ID` and `TRAN-DESC` tails come from uninitialized
  WORKING-STORAGE: `STRING` does not pad, and `TRAN-RECORD` has neither `VALUE` nor `INITIALIZE`.

`cbact04c_last_account_not_updated` (`Examples/Cbact04c.lean`) proves the first defect for
every one-account input. The input is any category balance, account, cross-reference and
disclosure group with a nonzero rate, any initial storage, and any clock reading. On such
input CBACT04C ends with `GOBACK` and writes one interest transaction, but never `REWRITE`s
the account. The account balance is not even an input to the theorem: it is never read.
The proof is symbolic execution through the whole program: five `OPEN`s, keyed `READ`s by
record and alternate key, `COMPUTE`, `STRING`, the timestamp, `WRITE`, five `CLOSE`s. The
loop is unrolled with `loopUntil_succ`. It checks in 15 s.
`Examples/Cbact04cSum.lean` proves the same theorem paragraph by paragraph. The account and
cross-reference lookups (`1100-GET-ACCT-DATA`, `1110-GET-XREF-DATA`) are each proved once as
summaries for any program with CBACT04C's configuration and files, and the main proof uses
them wherever the paragraphs run.

`cbact04c_two_accounts` (`Examples/Cbact04c2.lean`) covers two accounts with one category
balance each. CBACT04C rewrites exactly one record: account 1, with balance
`abal1 + divRound .truncation (bal1 * rate) 120000` (the monthly interest, truncated to cents)
and zero cycle credit and debit. It writes both interest transactions and never updates
account 2. This took one more automation step: numeric keys compared through their digit
characters are now decided by value (`digitChars_eq_eq` in `Cobol/Logic/Alnum.lean`). It
checks in 25 s. In the proved transaction records, the `TRAN-ID` prefix (`PARM-DATE`, from
the linkage section) and the tail of `TRAN-DESC` are visibly bytes of the initial storage.

`cbact04c_one_account` (`Examples/Cbact04cAny.lean`) removes the bound on the input length for
one account: any number of category balances (any types, categories and balances), each with
its disclosure group and any interest rate, zero included. CBACT04C ends with `GOBACK`, writes
exactly one interest transaction per category with a nonzero rate, and never `REWRITE`s the
account. The proof is by induction over the records (`cobol_loop`). The invariant (21 lines)
records what one iteration needs: the record count, the transaction-id suffix, the first-time
flag, the last account number, the account's group id and card number, a bound on the running
interest total, and the five file states. It holds before the loop, and one iteration
preserves it in four cases (first or later record, zero or nonzero rate), each by symbolic
execution and `cobol_inv`, which restates the invariant from its witnesses (the processed
records and, for the interest total, its new value). Before `cobol_inv`, most of the proof
restated the invariant's 20 components in each case: 155 lines, now 78. It checks in 41 s (the
previous proof: 56 s, on the same loaded machine).

`cbact04c_all` (`Examples/Cbact04cAll.lean`) is the theorem for every input: any number of
accounts (distinct ids), each with any number of category balances, with their account,
cross-reference and disclosure-group records found by key and any rates. CBACT04C ends with
`GOBACK` and writes one interest transaction per category with a nonzero rate. Its `REWRITE`s are
exactly the accounts before the last one, in input order. Each is rewritten with balance
`bal + total` (high-order truncated to the field, as an `ADD` without `ON SIZE ERROR` does) and
zero cycle credit and debit, where `total` is the account's monthly interest summed category by
category with CBACT04C's own truncations (`totalInt`). The last account is never updated. The
input model is a list of accounts (`Acc`: record fields, cross-reference record, category
balances). The category file is their records in order, and the account file is any file in
which each account's record is found by its key. The invariant (31 lines) tracks the accounts
already posted, the current account and its processed records, and the account file as seen by
key lookups (a `REWRITE` keeps every key, so lookups are unchanged: `findKey_set`). One iteration
preserves it in eight cases: the first record, a later record of the same account, the first
record of the next account (which runs `1050-UPDATE-ACCOUNT` and its `REWRITE` for the previous
one), and end of file, each with a zero or nonzero rate. Every case is proved by symbolic
execution (`cobol_auto`, which takes the case's facts from the context) and `cobol_inv`, given
the case's witnesses (the posted accounts, the current one, the processed records). By hand
remain only two facts about the `REWRITE` of the previous account: it keeps every record key
(`findKey_set`) and leaves the other accounts' records alone (`getD_set_ne`). A loop-invariant fact about a whole record
(`st.mem.read 956 300 = cur.bytes`) answers every read of one of its fields through
`Mem.read_of_read_sub`. The file checks in 50 s.

`cbact04c_events` (`Examples/Cbact04cEvents.lean`) fixes the whole event list for the same
inputs: every `DISPLAY`, every transaction record written (all 350 bytes) and every account
record rewritten, in order. The model `model4` is a fold over the category-balance records:
`DISPLAY` the record, `REWRITE` the previous account when the account changes, and for a nonzero
rate add the monthly interest and `WRITE` its transaction. The transaction record (`txRec`)
contains bytes the program never sets: the last 76 bytes of `TRAN-DESC` (`STRING` does not pad)
and the `FILLER` of `TRAN-RECORD`. They are parameters of the model (the initial storage's
bytes), as is `PARM-DATE` from the linkage section, so the theorem holds for every initial
storage, including the conventions of a test harness. The proof is `cbact04c_all`'s, with the
event list in the invariant instead of the two projections; `cobol_inv` closes the new parts.

`cbact04c_every` (`Examples/Cbact04cEvery.lean`) drops the lookup hypotheses of `cbact04c_events`:
the account, cross-reference and disclosure-group files are arbitrary lists of well-formed
records, read by key as the program reads them. The model `model4x` adds the paths the earlier
theorems leave out: a missing account or cross-reference record abends (code 999) after
`ACCOUNT NOT FOUND`, the error line, the status `0023` and `ABENDING PROGRAM`; a missing
disclosure group displays `DISCLOSURE GROUP RECORD MISSING` and `TRY WITH DEFAULT GROUP CODE` and
takes the rate of group `DEFAULT` instead, and a missing `DEFAULT` group abends. CardDemo's sample
data takes that `DEFAULT` path for every record: every account's `ACCT-GROUP-ID` is blank and the
disclosure file holds only the groups `A000000000`, `DEFAULT` and `ZEROAPR`, so the sample run is
outside `cbact04c_events`'s hypotheses and inside `cbact04c_every`'s. The model agrees with the
semantics on 12 runs (the sample data with zeroed and patterned storage, missing accounts,
cross-references and `DEFAULT` groups, zero rates, an empty file). The remaining assumption besides
well-formed records is distinct account ids among the category records, which a key-ordered read
of the KSDS gives. It checks in 468 s.

`cbtrn01c_verifies` (`Examples/Cbtrn01c.lean`) is about CBTRN01C, the daily transaction
verification. The input is any daily transaction file (any number of 350-byte records), any
cross-reference file of valid records, any account file of 300-byte records, and any initial
storage. On it CBTRN01C ends with `GOBACK`. Its `DISPLAY` output is the start message, each
transaction followed by what its two keyed lookups display, the lookups of the last transaction
once more, and the end message. `lookupMsgs` states what the lookups display: the
transaction's card number is looked up in the cross-reference file and, when found, the card's
account in the account file. The repetition comes from the loop body: only the `DISPLAY` of the
record is guarded by the end-of-file test, so after the end-of-file `READ` the lookups run
again on the record that `READ … INTO` left in WORKING-STORAGE (its initial contents when the
file is empty). The proof is a loop invariant (15 lines), symbolic execution (`cobol_auto`)
and `cobol_inv`. One iteration preserves the invariant in six cases: a record or the end of
file, each with the card not in the cross-reference file, the card found but not its account,
or both found. In each case the only input is the witnesses: the transactions read so far and
those still to come. It checks in 14 s.

`cbtrn02c_posts` (`Examples/Cbtrn02c.lean`) is about CBTRN02C, the daily transaction posting.
The input is any daily transaction file (valid records with distinct ids), any cross-reference,
account and category balance files, any clock and any initial storage. On it CBTRN02C ends with
`GOBACK`, its whole event list is the model's, and RETURN-CODE is 4 exactly when a transaction
was rejected. The model (`model`) is a fold over the transactions: look up the card and its
account, check the expiration date and the credit limit, then either write a reject record with
its reason code (100, 101, 102 or 103) or post the transaction. Posting creates or rewrites the
category balance record, rewrites the account, and writes the transaction record with the
clock's timestamp. Bytes the program never sets are model parameters: the `FILLER` of
`TRAN-RECORD`, and the initial `FILLER` of `TRAN-CAT-BAL-RECORD`, which new category records
inherit. The model gives the same 878 events as the semantics on CardDemo's 300 sample
transactions. The proof has eight iteration cases (end of file, four rejects, four postings:
new or existing category record, credit or debit). Each is symbolic execution and `cobol_inv`,
with one fact proved by hand: the transaction file holds only ids of earlier transactions, so
the posting `WRITE` never meets a duplicate key. It checks in 1m40s.

`cbtrn02c_any` (`Examples/Cbtrn02cDup.lean`) drops the distinct-ids hypothesis. A posted
transaction whose id was already written this run makes the `WRITE` fail with status 22
(`ACCESS MODE IS RANDOM`): the program displays the error and the status and abends (code 999),
after that transaction's category balance and account have been rewritten. Rejected
transactions are never written, so their ids do not collide. The model `modelX` is the posting
fold with this stop; without a duplicate it is `model`, and the conclusion is that of
`cbtrn02c_posts`. The proof uses `cobol_loop_exit` (`Cobol/Logic/LoopExit.lean`), the loop rule
for iterations that may leave the loop. The model agrees with the semantics on 9 runs: the
sample data, and duplicates placed at several distances, as debits, and as rejected copies.

`cbact01c_extracts` (`Examples/Cbact01c.lean`) is about CBACT01C, the account file extract. It
holds for any account file (valid records) and any initial storage, with the environment that
supplies COBDATFT (`Cobol/Ext/CardDemo.lean`). CBACT01C ends with `GOBACK`, and its event list is
a fold over the accounts: per account, the `DISPLAY`s, the output record (with COMP-3 fields),
the array record, the two variable-length records, and the `CALL` of COBDATFT. Two output bytes
come from storage the program never sets: two bytes of COBDATFT's output date. And
`OUT-ACCT-CURR-CYC-DEBIT` is set only when the account's cycle debit is zero, so otherwise the
previous record's value is written again; the model carries it from record to record. The model
gives the same 1 002 events as the semantics on CardDemo's 50 sample accounts.

`cbtrn03c_report` (`Examples/Cbtrn03c.lean`) is about CBTRN03C, the transaction detail report.
It holds for any non-empty transaction file (valid records), any cross-reference, transaction
type and category files, any date-parameter record and any initial storage, within the
program's domain:
- every transaction's processing date lies in the parameter's range. TRANREPT.jcl's SORT step
  selects exactly those; a date outside it ends the report early through `NEXT SENTENCE`;
- every lookup finds its record (otherwise the program abends);
- no card number is blank (blank is the initial value of the current card).

On such input CBTRN03C ends with `GOBACK`, and its whole event list is the model's: the start
message, the date range, a fold over the transactions (`step3`: page headers, a page total
every 20 lines, the previous card's account total at each new card, the detail line with the
type and category descriptions), then the end-of-file events. At end of file the last
transaction's amount is added to the totals again, so the last page total and the grand total
count it twice, and the last card's account total is never written; the theorem states both
for every input. The model gives the same 718 events as the semantics on CardDemo's data. The
proof has an end-of-file case and five record cases (the first record; the same card or a new
one, each with or without a page break), each closed by symbolic execution and `cobol_inv`. It
checks in 1m28s.

`cbtrn03c_stops` (`Examples/Cbtrn03cStop.lean`) covers the inputs outside that first domain
condition: in-range transactions `pre`, then a transaction `t0` outside the range, then
anything. The date check's `ELSE NEXT SENTENCE` passes control to the statement after the
period that ends the `PERFORM UNTIL … END-PERFORM` sentence, so `t0` ends the loop: it is neither
displayed nor reported, no page, account or grand total is written, and the program closes its
files and ends with `GOBACK`. The events are the start message, the date range, the report of
`pre` (the same `report3`), and the end message. Lookups and card numbers are constrained only
for `pre`. The proof reuses the five record cases and adds the exit through `cobol_loop_exit`;
it checks in 81 s.

`cbtrn03c_any` (`Examples/Cbtrn03cAny.lean`) covers every input with no blank card number: no
date or lookup hypothesis, and the transaction file may be empty. The model `report3x` follows the
program's order for each transaction: a date out of range stops the report (as in
`cbtrn03c_stops`); otherwise the record is displayed, a new card writes the previous card's
account total and looks up the cross-reference, then the type and the category are looked up. A
failed lookup abends (code 999) after its message, the status `0023` and `ABENDING PROGRAM`.
Otherwise the transaction is reported as by `step3`. At end of file the last record is tested
again: for an empty file that is the record area's initial contents, a model parameter. The
model agrees with the semantics on 23 runs: the sample data, dates out of range, missing cards,
types and categories at several positions, and the empty file. The proof has four end-of-file
cases, the five record cases, and eight abend cases; it checks in about 2 minutes.

`cbtrn03c_every` (`Examples/Cbtrn03cEvery.lean`) drops the last condition, the non-blank card
numbers. `WS-CURR-CARD-NUM` starts as spaces, so leading blank cards count as the same card: they
are reported without a cross-reference lookup, with the account id still in storage. That id is
a model parameter `x0` (the fold starts from `init3 x0`), constrained only when the first card
is blank; a blank card later is a new card and is looked up like any other. `result3_every`
shows that when the first card is not blank the outcome is `cbtrn03c_any`'s. The model agrees
with the semantics on 13 runs: blank leading cards (1, 2, 25, all), a blank card later, blank
first cards with failed lookups or a date out of range, and the sample data, with zeroed or
patterned storage. It checks in under 4 minutes.

## Writing an equivalence proof

1. **Extract** the program to surface JSON with `tools/cobolfe/cobolfe.py`. The front end
   handles fixed and free format, `COPY` (nested, `OF`/`IN` a library directory, `REPLACING`
   with pseudo-text, identifiers, literals, words and `LEADING`/`TRAILING` partial words) and
   `REPLACE` (processed after `COPY`, until the next `REPLACE`, `REPLACE OFF` or the end of its
   program), qualified names, level-88 and index names,
   abbreviated combined conditions, `EVALUATE … ALSO`, all `PERFORM` forms, arithmetic
   statements, files, and `STRING … DELIMITED BY SIZE`, which it lowers to reference-modified
   moves because the positions are static. A source with nested or batched programs gives one
   IR, the first program with the others linked in (`tools/cobolfe/unit.py`; with several
   separately compiled programs it also writes `OUT.link.json` for `link.py`). A program with
   `REPLACE` or with `COPY … REPLACING`, `OF` or `IN` is read on IBM's text words
   (`tools/cobolfe/textmanip.py`): separator commas and semicolons count as spaces when
   matching, words match in either case and literals character for character, debugging lines
   take part in matching before they become comments, and a replacement adds no spaces, so
   `==:TAG:== BY ==PAY==` turns `:TAG:-WEEK` into `PAY-WEEK`. A literal continued over several
   lines holds the spaces through column 72 of every continued line, as IBM's continuation rule
   says. Until 2026-10-27 the front end kept only the first line's, which shortened literals
   continued over three or more lines whose middle lines end before column 72
   (`tools/difftest/cont_cases/v_contlit.cob`, row V.contlit): 367 literals in 359 NIST
   programs, all report column headers (`CCVS-C-1`) or information lines except SM201A's
   `COPY-TEST-11` comparison, and none in CardDemo. As in GnuCOBOL, a sign written directly
   before digits always begins a literal and a comma or semicolon separates operands:
   `FUNCTION MAX(A, -3)` and `FUNCTION MAX(A -3)` have two arguments, `T(I -1)` has two
   subscripts, and `COMPUTE X = A -3` is rejected. The contract is `Cobol/Frontend/Surface.lean`.
   The front end only resolves names. Offsets, lengths, encodings, `REDEFINES` overlays,
   level-88 values, `EVALUATE` and `INITIALIZE` lowering, and the intermediate-scale rules all
   happen in Lean (`Cobol/Frontend/Resolve.lean`).
2. **Validate the extraction.** Run the COBOL source under GnuCOBOL and the IR under
   `cobolrun` on random inputs, and compare storage bytes and output files. See
   `examples/*/validate.py`.
3. **Load** it with `cobol_program P from "p.json"`. This defines `P`, one constant per
   paragraph named after it (`P.«1000-READ»`), and one per statement, named after its
   paragraph (`P.«1000-READ».s0`, …). Facts about a paragraph therefore keep their
   statements when other paragraphs change. It also registers the equations symbolic
   execution needs, and defines a reducible `P.FIELD : FieldDesc` and `P.FIELD.fmt : NumFmt`
   for every uniquely named data item.
4. **Transcribe** the Java or Rust method into Lean over the target models, one `def` per
   method. Use `Except` for exceptions and panics, and `match`/`if` rather than lambdas.
   Validate the transcription against the real code; `tools/targettest/targettest.py` runs
   JDK and rustc.
5. **State** the theorem. Inputs come from hypotheses `decodeNum {} P.F.fmt (m.field P.F) = some x`
   (and `m.field P.G = bytes` for alphanumeric items). Outputs are an observation function
   reading the final storage, compared with the transcribed method's result.
6. **Prove** it with `cobol_ranges`, the arithmetic identities between different rounding
   pipelines (as `have`), and `cobol_equiv [observation defs, method defs, input hypotheses]`.
   For binary items under bit-level rewrites, use `cobol_bv`.

### Summaries: prove a paragraph once

A paragraph can be proved once and reused at every `PERFORM` of it (`Cobol/Logic/Summary.lean`).
A summary is an equation for running the paragraph's sentences:

```lean
theorem getNext_record (P : Program) (hcfg : P.cfg = Cbact02c.cfg)
    (hfiles : P.files = Cbact02c.files) … (hr : recs[pos]?.isSome = true) … :
    Sem.execSentences P env rec fuel Cbact02c.«1000-CARDFILE-GET-NEXT».body ⟨m, …⟩ =
    (.normal, ⟨getNextMem m (recs[pos]?.getD []), …, [(1, { … pos := pos + 1 … })], …⟩)
```

It is stated for an abstract program `P`: only what the paragraph uses is assumed, so the
summary does not depend on the rest of the program. It is proved by `cobol_sym` (under a
second here). Registered with `attribute [local cobol_eval high] getNext_record`, it is used
by symbolic execution wherever the paragraph runs, instead of executing its statements.
Paragraph bodies are unfolded only when they run (`P.«paragraph».exec`), so the summary meets
`execSentences P … P.«paragraph».body st` at every call site. Its side conditions must be
dischargeable by `simp`. `performOnce_para'` gives the same fact for the `PERFORM` statement,
adding IBM's return-slot bookkeeping, for statements about ranges.

**Derived summaries.** The right-hand side does not have to be written by hand
(`Cobol/Logic/Derive.lean`):

```lean
cobol_summary getAcct_found (P : Program) (hcfg : P.cfg = Cbact04c.cfg) … (i : Nat)
    (hi : Sem.findKey { off := 0, len := 11 } (m.read 150 11) accts = some i)
    (hrec : (accts.getD i []).length = 300) :
    Sem.execSentences P env rec fuel Cbact04c.«1100-GET-ACCT-DATA».body ⟨m, …⟩
  using [hcfg, hfiles, hm, hi, hrec]
```

The command runs `cobol_sym` on the left-hand side and adds the theorem with the computed
right-hand side. It also prints that right-hand side: the paragraph's effect on the state,
in terms of the binders, as a reading aid. Only the paragraph, the shape of the state and the
hypotheses are written. A binder that the left-hand side does not determine, such as the
record number `i` of a keyed read, can stay a plain variable when a hypothesis pins it down.
At a call site, simp rewrites the side condition `Sem.findKey … = some ?i` with the call
site's facts to `ai = ?i`, and its discharger assigns `?i`. The two lookups of CBACT04C
(`Examples/Cbact04cSum.lean`) are derived this way. The main theorem uses them unchanged.

### Tactics

| Tactic | Does |
|---|---|
| `cobol_sym [h…] (at loc)` | symbolic execution. One `simp only` pass over the semantics with a curated set, simprocs for state merging, interval bounds and ground evaluation (`decodeNum` on literals, CP037). Data-dependent branches become value-level `if`s. |
| `cobol_auto [defs…]` | `cobol_sym` plus every usable fact of the local context: equations with an application on the left (lengths, storage contents, key lookups, file fields), negated equations, and the field reads implied by a whole-record fact (`Mem.read_of_read_sub`). A fact whose left side occurs inside another fact's left side is left out, so the more specific one can fire. Quantified hypotheses and equations with a variable on the left are not collected; pass them, and the definitions to unfold, in the list. `cobol_auto?` reports what it used. |
| `cobol_summary name binders : lhs using [h…]` | adds the summary theorem `lhs = rhs` with `rhs` computed by `cobol_sym` (see *Summaries*) |
| `cobol_ranges` | adds `h_range : bounds of x` for every `decodeNum … = some x` hypothesis |
| `cobol_equiv [h…]` | `cobol_sym` with the Java/Rust model sets (`java_eval`, `rust_eval`), then `cobol_grind` |
| `cobol_grind` | `grind` with the scaled-integer definitions (`divRound`, `fitNum`, …) and a larger split budget |
| `cobol_arith` | unfold rounding/truncation, split, `omega`; for lemmas like `daily_rate_eq` |
| `cobol_bv [h…]` | symbolic execution, `BitVec` restatement of binary items (`cobol_bits`), `bv_decide` |
| `cobol_loop Inv xs` | replace a `PERFORM … UNTIL` over the input items `xs` by its result, given the loop invariant `Inv`; adds the four induction obligations |
| `cobol_inv [defs…] with w…` | prove a loop invariant after symbolic execution of one iteration, from its witnesses. Conjunctions are split, existentials take the witnesses `w…` in order (`_`: found by unification, as the file states in `st.files = [(1, f₁), …]` are), a disjunction takes the side not refuted (a side is refuted when one of its parts simplifies to `False`). Each part is closed by `rfl`, an assumption, `cobol_auto [defs…]` (then `decide +kernel` if it leaves a ground goal), `cobol_simp_facts [defs…]` (then `omega`), or both in turn. Parts that do not close are left as goals. |
| `cobol_simp_facts [defs…]` | `simp [defs…]` with every fact of the context, the left side of each equation also in the simp normal form, and without `List.getD_eq_getElem?_getD` (the file model and the case facts use `List.getD`); for the list reasoning symbolic execution leaves (`flatMap`, `filterMap`, `reverse`, lengths) |
| `cobol_run [h…]` | symbolic execution with path splitting (one goal per path) |

## How it scales

The cost of an equivalence proof should grow with the size of the program, not with the
number of paths through it. Five mechanisms in `Cobol/Logic/` keep it that way:

* **Lazy evaluation of the interpreter.** The semantics is written with `match`/`if` and no
  continuation lambdas. Partially applied functions are unfolded only through fully applied
  equations. `matchItePre` distributes a `match` over an `if` before its arms are simplified,
  so each arm is evaluated only on a concrete scrutinee. The program is a constant: paragraph
  bodies are unfolded on demand and never copied into terms.
* **State merging** (`Merge.lean`). After an `IF` whose branches both continue normally, the
  results merge into one state whose fields are `if`s. Execution then continues once instead
  of once per path. Results with different control signals (a `GO TO` in one branch) are not
  merged; the `match` on the signal is distributed instead.
* **Flat memories** (`MemNorm.lean`). Storage is a chain of writes on the initial storage. The
  chain is kept with at most one write per field, in increasing offset order. A field written
  again replaces its earlier write (`normWrite`). The two memories of a merged `IF` become one
  chain over their common part, with value `if c then a else b` for each field written in
  either branch (`mergeMemIte`). A read then passes the fields written so far, not the
  statements executed so far. Hand-written summaries must state their memories in this order;
  derived summaries (`cobol_summary`) get it automatically.
* **Interval bounds** (`Bounds.lean`). Every store produces `fitNum c f v` (high-order
  truncation and the size-error test). Every read after a store produces
  `decodeNum (encodeNum v)`. When the interval of `v` fits the item, both become the
  identity. The intervals come from:
  - literals and input ranges;
  - `+ - *`, division by literals, `divRound` in any mode (all rounding modes are monotone), `natAbs` and `if`;
  - stored values, which are within the item's capacity.

  The same intervals decide target-language overflow checks such as `checked_mul` and
  `Math.multiplyExact`. Impossible size-error branches disappear, and the COBOL side becomes
  the arithmetic a faithful rewrite computes, so equivalence is closed by congruence rather
  than by case splits.

  Each step is a lemma application with `decide`-checked literal side conditions, so the
  kernel re-checks it.
* **Equation lemmas instead of smart unfolding** for the structurally recursive parts of the
  semantics. Lean's smart unfolding walks and copies every argument, including the merged
  symbolic state, which is a DAG of linear size but a tree of exponential size.
* **Nothing the kernel can run.** `Sem.loopUntil` is defined by well-founded recursion, so
  the kernel cannot unfold it. With a structural definition, the kernel's definitional checks
  on a goal stopped in front of a loop with fuel `n + k` ran `k` iterations of the loop body:
  279 s of kernel time for CBACT04C's prologue, 3.6 s now. Statements are separate constants,
  unfolded only when executed, so the part of the program still to run never appears in
  goals as literal text. `set_option profiler true` separates simp time from kernel time.

When symbolic execution is slow, the cause so far has always been a fact simp could not
decide, so that an `IF` stays open and both branches are simplified. The worst case is a byte
list of unknown length (CBACT04C's account group id, moved into a key): every memory access
behind it is undecided, simp simplifies both branches under the congruence lemma for `if`, and
its type checks evaluate memory reads by unfolding. A stack sample of the Lean process (gdb)
then shows `Simp.processCongrHypothesis` above the slow frames. Passing the missing fact (here
`grp.length = 10`) turns a 9-minute timeout into 11 s. The same symptom comes from a stored value
without a bound. Lean elaborates `((a + b : Nat) : Int)` as `↑a + ↑b`, so the interval code needs
a bound for each summand (`a < K`, `b < K`), not one for the sum.

Benchmarks (`bench/`), each proved equal to a Java-style fold:
- `seqif.py N`: *N* sequential `IF F-i > 0 ADD 1 TO CNT ADD F-i TO TOTAL END-IF`;
- `perfs.py N`: `MAIN` performs *N* paragraphs, each with an `IF … ELSE` and two arithmetic statements.

Cost of the whole proof in thousands of heartbeats (deterministic; `kHB` printed by the file),
before and after flat memories:

| N | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| `seqif` (3N statements), chains of merged stores | | 39 588 | 118 648 | 459 584 | |
| `seqif`, flat memories | 13 643 | 28 722 | 64 069 | 156 128 | 425 531 |
| `perfs` (N paragraphs, 5N statements), chains of merged stores | | | 137 863 | 545 594 | |
| `perfs`, flat memories | | | 58 774 | 128 734 | |

With chains of merged stores the cost quadrupled per doubling of N, because every field read
walked the whole history of `IF`s. With flat memories reads are independent of the history.
`perfs` now grows about linearly (×2.2 per doubling) and `seqif` by ×2.4 to ×2.7. For `seqif`
with N = 64 the CPU time drops from 75 s to 18 s. The rest of the growth comes from the values
themselves: after N `IF`s, `TOTAL` is a nested conditional sum of N terms, and simp's
unification walks such terms. Abstracting intermediate values into fresh variables (SSA-style
symbolic execution) is the next step. Without merging and bounds, `seqif` with N = 8 did not
finish within the default heartbeat budget (exponential path explosion).

## Validation of the semantics

The semantics is the specification, so it is tested against GnuCOBOL 3.2. GnuCOBOL is
unpacked from the <os-image> packages into `third_party/`; use `scripts/cobc.sh`. Run with the
IBM-compatible profiles `-std=ibm -fbinary-truncate -fno-arithmetic-osvs` for TRUNC(STD) and
`-std=ibm -fno-arithmetic-osvs` for TRUNC(BIN).

| Suite | Result |
|---|---|
| `difftest.py` random data/arithmetic programs, TRUNC(STD) | 800/800 agree (14 only in the stored sign of an equal value: a negative zero, or sign nibble F vs C after a `MOVE` from an unsigned packed item) |
| `difftest.py --trunc bin` | 794/800; the 6 are GnuCOBOL's inconsistent handling of out-of-`PICTURE` binary values |
| `ctrltest.py` random `PERFORM`/`GO TO` programs | 531/600 agree, 0 disagree, 69 declined (recursive `PERFORM` or return into an abandoned `PERFORM`: reported as unsupported) |
| `examples/acctint/validate.py` (IR vs source) | 200/200 |
| `examples/binary/validate.py` (IR vs source, overflow cases) | 100/100 |
| `examples/recsum/validate.py` (IR vs source, real sequential files of 0 to 30 records) | 50/50 |
| `tools/targettest/targettest.py` (Lean transcriptions vs JDK / rustc) | 500/500 |
| front end: `examples/*/validate.py --ir` on front-end IRs of ACCTINT, BINCNT, RECSUM | 40/40 each |
| front end: `difftest.py --frontend` (the same random COBOL, extracted by `cobolfe`) | 60/60 |
| front end: `ctrltest.py --frontend` | 53/60 agree, 0 disagree, 7 declined (recursive `PERFORM`) |
| front end: `tools/difftest/fn_cases/fnsign1.cob` (signed literals and separators in function arguments, subscripts and operand lists; `filetest.py --run`) | 30/30 lines agree |
| front end: `tools/difftest/link_check.sh` (linked programs: `EXIT PROGRAM`, equal section names, a callee that calls another program) | 3/3 agree |
| front end: `tools/difftest/nestedtest.py` (nested and batched programs, `GLOBAL`, `EXTERNAL`, `CALL` forms, `INITIAL`, `CANCEL`; below) | 60/60 at seeds 1 and 2 |
| front end: `tools/difftest/corrtest.py` (`MOVE`/`ADD`/`SUBTRACT CORRESPONDING` and level-66 `RENAMES`, seeds 1 and 2) | 60/60 each |
| front end: `tools/difftest/unsup_check.sh` (each construct of *Unsupported programs* faults at the first statement or is rejected; 23 controls run) | 79/79 |
| `tools/difftest/sysintest.py` (`ACCEPT` from the system input device, against GnuCOBOL with the deck as standard input and against the IBM rule; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/editpttest.py` (numeric editing with insertion characters around the decimal point, against GnuCOBOL and an IBM mirror; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/justtest.py` (`MOVE` into `JUSTIFIED RIGHT` items, group senders above all; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/displittest.py` (`DISPLAY` of numeric literals; signed ones reported unsupported; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/lctest.py` (PICTURE character-strings that begin with a comma, against GnuCOBOL and an IBM mirror; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/closetest.py` (`CLOSE … REEL` / `UNIT`, `NO REWIND` and `LOCK`, `OPEN … REVERSED`, against GnuCOBOL and an IBM status mirror; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/powtest.py` (powers whose exponent is an integral data item or expression, against GnuCOBOL and an IBM mirror; below) | 60/60 at seeds 1 and 2 |
| `tools/difftest/dmaxtest.py` (IBM's `dmax` and the places of a quotient, level-88 `VALUE ALL` literals, `ROUNDED MODE`; parts all88, cond, edited, intfn, div, fnarg, fncond, rmode, against GnuCOBOL and the tester's IBM lines or an IBM mirror; below) | 60/60 per part at seeds 1 and 2 |
| `tools/difftest/ir30test.py` (intermediate results that can need more than 30 digits, part ir30; powers by a literal exponent, part powlit; powers by the literal 0, part pow0; the composite of operands, part c30; against GnuCOBOL and an IBM mirror; below) | 60/60 per part at seeds 1 and 2 |

Where GnuCOBOL deviates from documented IBM Enterprise COBOL behaviour, the model follows
IBM and the test generators avoid the case:
- operands re-read in multi-receiver `ADD`;
- COMP size error by binary capacity;
- 1-byte COMP-5;
- `REMAINDER` after a quotient size error;
- `SUBTRACT ROUNDED` into COMP-3;
- `JUSTIFIED` with a longer numeric sender;
- editing of literals before truncation;
- `EXIT SECTION`;
- `INITIALIZE` of index data items, which IBM leaves unchanged and GnuCOBOL sets to zero;
- `SEARCH … VARYING` an index data item that does not start at the search index's value
  (GnuCOBOL sets it to the index's occurrence number, as it does an integer item);
- `=` and `<>` between two literals under a `PROGRAM COLLATING SEQUENCE` that puts both
  characters in one position (`ALSO`): GnuCOBOL compares the bytes (G-alsolit);
- `ORD` and `CHAR` under an `ALPHABET` of literals: GnuCOBOL uses the native order
  (G-ordchar);
- `NOT ON SIZE ERROR` without `ON SIZE ERROR`: GnuCOBOL leaves a receiver with a size error
  unchanged, IBM applies the truncation rules (NIST triage cause C1, also in `ADD`/`SUBTRACT
  CORRESPONDING`);
- index data items in `MOVE`/`ADD CORRESPONDING`: GnuCOBOL moves and adds them, IBM leaves them
  out (G-corrindex);
- a level-66 entry renaming one `COMP`, `COMP-3` or `COMP-5` item: GnuCOBOL gives it `DISPLAY`
  storage of the picture's digits, IBM all the attributes of the renamed item (G-renusage);
- `MOVE CORRESPONDING` pairs whose elementary `MOVE` IBM's table does not permit: GnuCOBOL moves
  a non-integer numeric item to an alphanumeric one and rejects a pair with an alphabetic item
  (G-corrmove; the model makes such a statement unsupported);
- `COPY … REPLACING` and `REPLACE`: GnuCOBOL never matches a pseudo-text-1 that is only a
  separator comma or semicolon (G-sepcomma), does not take a separator comma inside parentheses
  as a space (G-parencomma), matches literals in either case (G-litcase), drops debugging lines
  before matching unless they are compiled (G-dline), keeps blanks at the ends of pseudo-text-2,
  so that `== PAY ==` does not glue to `-WEEK` (G-ptblank), and rejects blanks inside
  partial-word delimiters (G-pwblank), which IBM's own examples use; cobc 3.2 aborts on an empty
  partial-word-2;
- a `REPLACE` statement in a source with several separately compiled programs: GnuCOBOL keeps
  it in effect in the programs that follow, IBM ends it with the `END PROGRAM` of its own
  program (G-replbatch, `tools/difftest/copyrepl_cases/g_replbatch.cob`);
- de-editing a `DB` sign, which GnuCOBOL ignores (G-deedit-db), and a `0` insertion character,
  which GnuCOBOL reads as a digit (G-deedit-zero);
- editing with a `0` or `/` insertion character in or right after a zero-suppression or floating
  string, which IBM counts as part of that string and GnuCOBOL keeps (G-editins; G-ins0 in
  `tools/difftest/dpc_cases/g_ins0.cob`, `editpt_cases/g_editins_pt.cob`), with a `B` or `,` right
  after the decimal point when the integer part is a suppressed zero, which GnuCOBOL writes as `0`
  (G-editptb, `editpt_cases/g_editptb.cob`), a negative value under a leading sign and a fixed
  currency symbol (G-editsigncur), and a floating `$` string before a fixed `+` or `-`
  (G-editfloatsign);
- a `,` with no digit position on its left (a PICTURE string that begins with a comma, or `B,ZZ9`):
  GnuCOBOL writes a space, IBM writes the `,` (G-editlc, `tools/difftest/lc_cases/g_editlc.cob`);
- `COMPUTE` and `ADD … GIVING` into a picture whose floating currency string has an insertion
  symbol right after its first symbol: GnuCOBOL drops the leftmost digit, which its `MOVE` keeps
  (G-floatcs);
- `BLANK WHEN ZERO` on a numeric item with `V`: GnuCOBOL makes the item one byte longer
  (G-bwzv);
- `ACCEPT` from the system input device: GnuCOBOL reads one line per `ACCEPT` and moves it as a
  `MOVE` would, so a receiver longer than the record is padded (G-sysin-long), numeric, edited and
  `JUSTIFIED` receivers get a converted, edited or right-justified value (G-sysin-num, G-sysin-edit,
  G-sysin-just), and at the end of the input it moves a space (G-sysin-eof); `sysintest.py`
  checks those lines against the IBM rule instead of GnuCOBOL.
- a power whose exponent is an integral data item or expression: IBM holds the power with `dmax`
  decimal places and, for a negative exponent, divides 1 by that value to `dmax` places, where
  GnuCOBOL computes the exact power (G-powtrunc, G-pownegdiv), and zero raised to a negative power
  is a size error, which GnuCOBOL computes as 0 (G-pow0neg); `powtest.py` checks those lines
  against its IBM mirror (`tools/difftest/pow_cases/g_pow*.cob`). GnuCOBOL 3.2 also compares an
  unsigned item with a negative value, and a negative literal or constant expression with an item,
  as if the value were positive (G-ucmpneg, G-negconst, `pow_cases/g_negcmp.cob`); the testers
  avoid both.
- quotients: GnuCOBOL -std=ibm's OS/VS rules (`arithmetic-osvs`) keep more places for a quotient
  than IBM's "(d2 - d1) or dmax, whichever is greater" in several shapes (a divisor with more places
  than `dmax`, a nested quotient, a divisor scaled by `P`, a quotient next to an integer function:
  G-osvsdiv; a quotient inside a function argument, whose `dmax` on IBM is the function's
  inner-dmax: G-fnarg, `MAX (D2 / N7, 0.05)` with D2 1.00 and N7 7 is 0.140000 on IBM, 0.142857 in
  GnuCOBOL), and give an `EVALUATE` subject the `dmax` of its relation with each object, where IBM
  evaluates it "without regard to the attributes of its comparand" (G-evalown;
  `tools/difftest/dmax_cases/g_*.cob`). With `-fno-arithmetic-osvs` GnuCOBOL computes quotients
  exactly; `dmaxtest.py` checks the lines where exact quotients give another value against its IBM
  lines or mirror (G-exactdiv).
- intermediate results of more than 30 digits: IBM keeps an intermediate result to 30 digits in
  compatibility mode, cutting the decimal places beyond those its table carries (G-ir30), and
  holds a power by a literal exponent of over 30 digits (or of 30 with an even number of digits in
  the base) with `dmax` decimal places (G-powlit), where GnuCOBOL computes exactly; `ir30test.py`
  checks those lines against its IBM mirror (`tools/difftest/ir30_cases/g_ir30_1.cob`,
  `powlit_cases/g_powlit_1.cob`). GnuCOBOL 3.2 also folds an integer literal raised to a literal
  exponent in 64-bit binary, so that `2 ** 64 / 1000` is 0 and `3 ** 40 / 100` is
  62890786146526228 (G-litpow64, `powlit_cases/g_powlit_1.cob`); those lines are checked against
  the IBM mirror only. Zero raised to the literal power 0 is a size error: under `ON SIZE ERROR`
  GnuCOBOL runs the imperative but stores 1 all the same, where IBM leaves the receiver unchanged
  (G-pow00), and it folds the literal `0 ** 0` to 1 with no size error (G-litpow00;
  `pow0_cases/g_pow0_1.cob`).

The difftests found several modelling errors, all fixed: paragraph versus section exit
points, `REMAINDER` using the truncated quotient, and recursive `PERFORM`. A deliberately
planted front-end bug (`-` extracted as `+`) failed 6 of 30 programs, so the front-end
checks are not vacuous.

What `difftest.py` observes: the final bytes of the working-storage record, including a
trace with one byte per statement (`OTRACE`) into which every `IF`/`ELSE`, `ON SIZE ERROR` and
`NOT ON SIZE ERROR` outcome is written, so that no later statement hides which phrase ran.
When the bytes differ although every field decodes to the same value, the test is
`ok-negzero` if a signed field holds zero with the other sign (packed `D` vs `C`, separate
`-` vs `+`, overpunch `p` vs `0`), `ok-packed-fc` if a signed packed field differs only in
its sign nibble `F` (GnuCOBOL, after a `MOVE` from an unsigned packed item) vs `C`, and
`mismatch-bytes`, a failure, in any other case. Each strengthened check was shown to catch a
planted model error that the earlier check missed (a skipped `NOT ON SIZE ERROR` phrase:
58 of 200 programs caught only through `OTRACE`; a positive separate sign stored as a space:
2 programs), and the unmutated model passes.

File I/O is tested by `tools/difftest/filetest.py`. It generates random programs with 1 to 3
sequential and indexed files and 10 to 32 `OPEN`/`READ`/`WRITE`/`REWRITE`/`DELETE`/`CLOSE`
statements, including misuse that yields error statuses. Each program records the status
code, which phrase ran, and the record area after every statement, and DISPLAYs that record
at once. GnuCOBOL (Berkeley DB indexed files) and the model must agree on the final storage
and on every DISPLAY line, also where an unhandled error abends: both must stop at the same
statement with the same status, and the lines of the statements before it must agree (the
final storage is lost there). A planted error in the status of a misplaced `READ` changed
only such pre-abend lines in one program, which only the line comparison caught.
- Results on 200 programs per seed: seeds 101 and 102 agree on all 200, counting 1 and 4
  agreeing abends. Seed 103 runs with nothing excluded: 160 agree, and the other 40 are
  instances of the GnuCOBOL deviations below. In every case both sides showed the status the
  classification predicts, and nothing was left unexplained.
- The tester found two model errors, both fixed: a failed `WRITE` after a `READ` must make the
  next sequential `REWRITE` fail with 43; a key below the previous one in sequential `WRITE`
  is a sequence error (21) before it is a duplicate (22).
- It found three front-end errors, all fixed: `NOT INVALID KEY` was parsed as
  `INVALID KEY`; `CLOSE … LOCK` and `WITH NO REWIND`, which it dropped, were made `unsupported`
  (since 2026-10-28 they are modelled: `closetest.py`, below).
- It documents eight GnuCOBOL deviations from IBM, which are excluded by default:
  - duplicate keys in sequential output give 21;
  - no highest-key check after `OPEN EXTEND`;
  - a failed `WRITE` still sets the previous key;
  - a changed key on `REWRITE`;
  - `REWRITE` with alternate keys;
  - `REWRITE` of a missing key gives 21;
  - `CLOSE` after `CLOSE WITH LOCK` (G-lockclose: 00 and the lock lifted, or a crash for an
    indexed file; IBM: 42);
  - a failed `OPEN` (41) does not forget the last `READ`.

  Reproducers are in `tools/difftest/filetest_cases/`. The IBM verdicts come from the manuals.
  No IBM system was available.
- Variable-length records (`filetest.py --run`). `v_varying_ok.cob` agrees on every line: `WRITE`
  of lengths in range and below the minimum (44), `READ` setting the `DEPENDING ON` item, the
  record read, and a `REWRITE` that changes the length (44). `c5_check.py` runs
  `tools/difftest/c5_cases/`, files whose record descriptions have different lengths (no `RECORD`
  clause; `RECORD VARYING DEPENDING ON` without bounds; `RECORD CONTAINS m TO n` with the shorter
  record first): all agree on every line. `g_varying.cob` documents three
  further GnuCOBOL deviations from IBM. A length above the maximum is written truncated (IBM:
  44). `READ … INTO` moves the whole record area (IBM: the record read). A same-length
  sequential `REWRITE` gives 44 (IBM: 00).

`INSPECT` is tested by `tools/difftest/inspecttest.py`. Each random program has 25 `INSPECT`
statements on 12-character items over a 4-letter alphabet, with 1 to 3 phrases, patterns of 1
or 2 characters or a figurative constant, delimiters, and two counters, which start from
non-zero values, so that a count stored instead of added shows (a planted model error of that
kind fails all 60 programs; with counters reset to zero, as before 2026-10-25, it failed none).
Seeds 1 and 2 agree on 60 of 60 programs each, 3 000 statements in all. This holds on the subset where GnuCOBOL's
implementation must give the standard result: multi-phrase statements use one-character
patterns and no `LEADING`. Outside that subset GnuCOBOL applies the phrases one at a time over
the whole item instead of the standard comparison cycle (at each position, the first phrase
that matches there). Reproducers are in `tools/difftest/inspect_cases/`:
- a later phrase whose pattern starts before an earlier phrase's match loses to it. `ALL 'A'
  BY 'y' ALL ' A' BY 'bx'` on `BABAX AXBBXA` gives `ByByX yXBBXy` (standard: `ByByXbxXBBXy`);
- positions of a `LEADING` run are counted again by later phrases (2 + 19 for 20 characters);
- a second `CHARACTERS` phrase, which can never apply, changes the result.

Signed numeric `DISPLAY` items are tested by `tools/difftest/inspecttest_signed.py` (rows
V.ins.s1 and V.ins.s2): 25 `INSPECT` statements per program on five signed items (embedded and
separate signs, leading and trailing, one with decimals), with `TALLYING`, `REPLACING` and
`CONVERTING`, after which both sides display the item's bytes. Seeds 1 and 2 agree on 60 of 60
programs each. Until 2026-10-27 the model inspected such items with their sign byte included:
NIST NC216A failed, and the same tester fails 119 of 120 programs on that version. The tester
leaves out one GnuCOBOL 3.2 defect, G-convempty: `CONVERTING` with an empty region (`BEFORE
INITIAL` at the first examined byte, or `AFTER INITIAL` absent) drops an embedded sign, although
nothing is converted.

Declaratives are tested by `tools/difftest/decltest.py` (rows V.decl.s1 and V.decl.s2): random
programs with one to three sequential or indexed files (some without `FILE STATUS`), one to
three `USE` declaratives on file names or open modes, and 10 to 24 I/O statements, many ending
in 10, 22, 23 or 41 to 49 with and without `AT END` / `INVALID KEY`; every statement and
declarative displays a trace. Seeds 1 and 2 agree with GnuCOBOL on all 60 programs each (about
500 declarative runs per seed). The version before 2026-10-27 rejects all 120 programs as
unsupported, and planted errors (an open-mode declarative taking precedence over one naming the
file; no declarative for a file with a `FILE STATUS` item) fail 4 and 50 of the 60 programs of
seed 1. Left out of generation, besides `filetest.py`'s classes: an error on a file that is not
open with only an open-mode declarative, where GnuCOBOL runs the declarative of the mode the
file was last opened in, while IBM applies an open-mode declarative to files open in that mode
(G-closedmode), and a `READ NEXT` after a failed keyed `READ` (G-readfail, see `dyntest.py`
below). Of the 43 NIST programs (30 SQ, 13 IX) that the earlier front end made
unsupported for their declaratives, 39 passed then; SQ215A passes since `CLOSE … WITH LOCK` is
modelled (its declarative sees the 38 of an `OPEN` after the lock), and SQ203A and IX218A
(unsupported then for `SELECT OPTIONAL`, next paragraph) and IX208A (for `START` by an alternate
key, see alternate keys below) pass since those are modelled.

`SELECT OPTIONAL` is tested by `tools/difftest/opttest.py` (rows V.opt.s1 and V.opt.s2): random
programs with one to three sequential or indexed files (`ACCESS RANDOM`, `DYNAMIC` or
`SEQUENTIAL`), at least one of them `OPTIONAL` and absent when the program starts (`cobolrun
--absent`), the others created with zero to four records by a GnuCOBOL setup program (`cobolrun
--inputs`), and 10 to 24 I/O statements, `OPEN` in every mode included; then every file is closed
and read back, and its `OPEN INPUT` shows whether it exists (00) or is still absent (05). Every
statement displays every file status and record area. Seeds 1 and 2 agree with GnuCOBOL on all
60 programs each. They open absent `OPTIONAL` files 75 and 84 times, 51 and 60 of them in
`INPUT`, `I-O` or `EXTEND` mode, all with status 05 on both sides. The version before 2026-10-27
rejects all 60 programs of seed 1 as unsupported, and four planted errors in `Sem.fileOpen`
(`tools/difftest/opttest_mutants.md`: absence ignored, `OPEN INPUT` creating the file, creation
forgotten, 05 for `OUTPUT`) fail 46, 11, 50 and 23 of the 60 programs of seed 1. Left out of
generation: a keyed `READ` as the first `READ` of an absent `OPTIONAL` file opened `INPUT`, where
GnuCOBOL gives 10 without running `INVALID KEY` (and a `READ NEXT` after it 46), while IBM gives
23, the invalid-key condition, and 46 for the `READ NEXT` (G-optkey,
`tools/difftest/opt_cases/g_optkey.cob`), and a `READ NEXT` after a failed keyed `READ`
(G-readfail, see `dyntest.py` below). `opttest.py --run` also runs `v_optional.cob`, which agrees
on every line, and `v_optional2.cob`, which agrees on every line but D3, a `READ NEXT` after a
failed keyed `READ` of the empty file just created (G-readfail: GnuCOBOL 10, the model 46). Of
the NIST programs with `OPTIONAL` files, SQ203A, IX217A and IX218A pass, where they were
unsupported before; IX217A tests the status 05 itself, and IC233A (a nested program) passes since
nested programs are modelled. The others stop for other reasons: SQ401M (its `LINAGE` clause) in
the front end and IX401M (a `RECORD VARYING` maximum above the record area) in the resolver;
IX216A passes since `CLOSE … LOCK` is modelled.

Nested and batched programs are tested by `tools/difftest/nestedtest.py` (rows V.nest.s1 and
V.nest.s2). Each random source has a main program, one to three programs it contains (some
`COMMON`, some containing a program of their own) and up to two further separately compiled
programs; they use `GLOBAL` data, condition names and indexes and local names hiding them, one
`EXTERNAL` record described with different subordinate items in several programs, `CALL` by literal
and by identifier of every program IBM's naming rules let them call, `BY REFERENCE` (also the same
item twice) and `BY CONTENT` arguments, `ON EXCEPTION`, `ON OVERFLOW` and `NOT ON EXCEPTION`,
`INITIAL` programs, `CANCEL` by literal and identifier, and `RETURN-CODE` passed back; half of the
sources have a `GLOBAL` file whose `USE GLOBAL` declarative of the main program a contained
program's `READ` triggers. Every program displays what it sees. Seeds 1 and 2 agree with GnuCOBOL on
all 60 programs each (seed 1: 282 programs, 406 `CALL`s, 212 of them by identifier, 56 `CANCEL`s, 29
`INITIAL` programs, 11 `CALL`s with a duplicated argument). The version before 2026-10-27 rejects
all 60 programs of seed 1, and eight planted front-end errors (`tools/difftest/nestedtest_mutants.md`:
`BY CONTENT` passed by reference, `EXTERNAL` not shared, a global name before the program's own,
`NOT ON EXCEPTION` dropped, `CANCEL` doing nothing, the duplicated-argument variant naming the
second parameter, `INITIAL` ignored, `RETURN-CODE` not passed back) fail 15, 43, 29, 52, 16, 5, 8
and 16 of the 60 programs of seed 1. The tester leaves out six GnuCOBOL 3.2 defects, with
reproducers in `tools/difftest/nested_cases/`:
- after a `USE GLOBAL` declarative has run for a contained program's I/O statement, later `CALL`s of
  programs called before fail or crash GnuCOBOL (G-declcall, `g_declcall.cob`);
- after a `CALL` of an `INITIAL` separately compiled program the caller's `RETURN-CODE` is 0, not
  the called program's (G-initialrc, `g_initialrc.cob`);
- the second `CALL` of an `INITIAL` separately compiled program from a contained program stops the
  run with "attempt to CANCEL active program" (G-initialnest, `g_initialnest.cob`);
- a `CALL` of an `INITIAL` contained program also resets the programs contained in its siblings
  (G-initialsib, `g_initialsib.cob`);
- a `CANCEL` of a returned `COMMON` program from a program contained in its sibling stops the run
  with "attempt to CANCEL active program" (G-cancelcommon, `g_cancelcommon.cob`);
- so does a `CANCEL` of a returned `INITIAL` program from a program other than its caller
  (G-cancelinitial, `g_cancelinitial.cob`).

`nestedtest.py --run` on the other cases there (`v_nested1`, `v_dupargs`, `v_cancel`,
`v_external_cancel`) agrees on every line, and on the six reproducers the model prints the IBM
result stated in each. Of the 16 NIST programs that nested or batched programs, `GLOBAL` and
`EXTERNAL` items, `CANCEL` or `CALL identifier` made unsupported, 12 pass now (IC201A, IC203A,
IC209A, IC213A, IC223A, IC224A, IC225A, IC226A, IC228A, IC233A, IC235A, IC237A). IC222A stops at
`CALL "XXXXXXXX" ON EXCEPTION` (availability), IC227A is unsupported for its `EXTERNAL` file, IC234A
stops at an I/O statement whose declarative IBM selects per program, and IC401M at `CALL "FIC401M"`,
a program that does not exist, called without `ON EXCEPTION` (undefined; GnuCOBOL abends). The IC
module passes 19 of its 25 programs (7 before).

`START` and dynamic access (`filetest_cases/v_start_dynamic.cob`) agree with GnuCOBOL on every
line. The case covers `START` with `=`, `>` and `NOT <` on a leading part of the key, a failed
`START` (23, then `READ NEXT` 46), `START` without `KEY`, a random `READ` followed by `READ NEXT`,
and a `WRITE` before the reading position. In dynamic access the file position indicator holds
a record key, as in the standard and GnuCOBOL: after `OPEN` the first record and after `START`
the record found are read next, even when a lower key is written in between; after a `READ` the
next higher key is read. So a record written at the reading position is read next only if its
key comes after the indicator (until 2026-10-26 the model kept the position as an index, and a
record written there was always read next; mutation testing found it).
`tools/difftest/filetest2_pos.py` (random `START`, `READ NEXT`, keyed `READ`, `WRITE`, `REWRITE`
and `DELETE` before, at and after the reading position) agrees on 100 of 100 programs at each of
seeds 51 and 52, and `pos_check.py` (20 hand-made scenarios) on all 20; the earlier model fails 4
of each seed's 100 and 9 of the 20. Random file programs (`filetest.py --n 60
--seed 102`) still agree on all 60.

Alternate record keys and `SAME RECORD AREA` are tested by `tools/difftest/alttest.py` (rows
V.alt.s1 and V.alt.s2): random programs with two or three indexed files (`ACCESS DYNAMIC` with a
unique and / or a `WITH DUPLICATES` alternate key, `ACCESS SEQUENTIAL` with a duplicates key, a
unique one or none, `ACCESS RANDOM` with a duplicates and / or a unique key), created with 0 to 7
records by a GnuCOBOL setup program (`cobolrun --inputs`), some of them sharing a record area,
and 15 to 35 `START` (`=`, `>`, `>=`, `NOT <` on the record key, an alternate key or a leading
part of one), `READ NEXT`, keyed `READ` by every key, `WRITE`, `REWRITE` and `DELETE`
statements; an epilogue reads every file in the order of each of its keys. Every statement
displays every file status and record area. GnuCOBOL 3.2 never gives status 02 (G-dup02), so the
tester also predicts every status from its own mirror of IBM's rules: a program passes when the
model's lines equal GnuCOBOL's once the predicted 02s are read as 00, and the model's statuses
equal the mirror's. Seeds 1 and 2 pass on all 60 programs each; in their random parts 32 and 43
`READ`s and 40 and 40 `WRITE`s and `REWRITE`s give 02. The version before 2026-10-27 passes none
of seed 1 (51 programs stop at `START` by an alternate key or `READ` by an alternate key with
duplicates, 9 are unsupported for `SAME RECORD AREA`), and five planted errors
(`tools/difftest/alttest_mutants.md`: duplicates in record-key order, no 02 after a `READ`,
`START` by an alternate key in record-key order, the record read read again, `SAME RECORD AREA`
without effect) fail 14, 46, 46, 57 and 9 of the 60 programs of seed 1. Left out of generation,
where GnuCOBOL departs from IBM: a `REWRITE` in sequential access of a file with a unique
alternate key (G-rwalt; the failed `REWRITE` also drops the record from GnuCOBOL's alternate
index), a `REWRITE` of a missing record key (G-rw21), and a `READ NEXT` after a failed keyed
`READ` (G-readfail: GnuCOBOL continues where it was, repeats or skips records, or gives 46; IBM's
status table gives 46, and so does the model; next paragraph). `alttest.py --run
tools/difftest/alt_cases/*.cob` runs the hand cases: four
agree with GnuCOBOL on every line (02 read as 00), and the reproducers of G-rwalt and G-readfail
differ as documented. In the NIST suite IX205A to IX215A, SM203A and SQ206A pass, where they
were unsupported for `START` by an alternate key, `READ` by an alternate key with duplicates or
`SAME RECORD AREA` (IX210A, IX214A and IX215A also need `PROGRAM COLLATING SEQUENCE`, below), and
so does SM204A, which reads SM203A's file and failed without it (io 35).

A `READ NEXT` after a failed keyed `READ` in dynamic access is tested by
`tools/difftest/dyntest.py` (rows V.dyn.s1 and V.dyn.s2). IBM's file status table gives 46 for a
`READ NEXT` when "The preceding READ statement was unsuccessful but did not cause an at-end
condition", and its `READ` notes say that after an unsuccessful `READ` "the value of the file
position indicator [is] undefined"; only `OPEN`, `START` and `READ` set it again. The random
programs have two or three indexed files (`ACCESS DYNAMIC` without an alternate key, with a unique
alternate key the program never names, or with a `WITH DUPLICATES` key; a second `ACCESS DYNAMIC`
file; in most programs an `ACCESS SEQUENTIAL` one), created by a GnuCOBOL setup program, and 15 to
35 `START`, `READ NEXT`, keyed `READ` (key in the file or not), `WRITE`, `REWRITE`, `DELETE` and
`CLOSE` + `OPEN` statements, `READ NEXT` weighted up after a failed keyed `READ`. Every statement
displays every file status and record area. The tester predicts every status with `alttest.py`'s
mirror of IBM's rules. Where GnuCOBOL 3.2 departs from IBM, a `READ NEXT` after a failed keyed
`READ` (G-readfail: it continues where it was, repeats or skips records, or gives 46), the file's
status and record area are compared with the mirror only; every other line must equal GnuCOBOL's.
Seeds 1 and 2 pass on all 60 programs each, with 175 and 121 such `READ NEXT`s (GnuCOBOL gave 00,
10 and 46 on 74, 22, 79 and on 24, 21, 76 of them). The version before 2026-10-27, which continued
from the earlier position on files without `FileDecl.keyRef`, fails 28 and 26 of the 60 programs,
as GnuCOBOL does, and six planted errors (`tools/difftest/dyntest_mutants.md`) fail 28, 11, 2, 5, 4
and 21 of the 60 programs of seed 1. `opttest.py` and `decltest.py` now leave G-readfail out of
generation too. At the seeds of their rows this changes 5 and 11 programs, the only ones with such
a `READ NEXT`: in 3 of them (OT02055, DT02038, DT02053) the earlier model had agreed with GnuCOBOL
on 10 where IBM gives 46, and in the others the `READ NEXT` gives 47 or 46 either way. In the NIST
suite no supported program reads a file of the record-key path with `READ NEXT` after a failed
keyed `READ`; the 13 programs with dynamic files have the same outcomes and output as before.

`SEARCH` (`tools/difftest/search_cases/`, `filetest.py --run`): `srch1.cob` agrees on every line.
It covers a hit, a search from a later index, `AT END`, two `WHEN`s, a start past the table,
`VARYING` an index of the same table, and no `AT END`. One GnuCOBOL deviation is documented
(`g_search_varying.cob`). IBM increments an integer `VARYING` item by one with each step of
the index; GnuCOBOL sets it to the occurrence number. `SEARCH ALL` (`srchall1.cob`) agrees on
every line: hits and misses with two ascending keys, and a descending numeric key.
`u_searchall_undefined.cob` shows why an out-of-order table is `unsupported`. There
GnuCOBOL's binary search reports `AT END` although the element is present.

`UNSTRING` is tested by `tools/difftest/unstringtest.py`. Each random program has 25 statements
on 14-character items over `AB,; `, with 1 or 2 delimiters (`ALL` or not), 1 to 3 receivers with
optional `DELIMITER IN` / `COUNT IN`, `POINTER` values inside and outside the item, `TALLYING`
and both overflow phrases. After each statement every receiver, delimiter and count, the
pointer, the tally and the phrase that ran are displayed, and the counts and the tally start
from non-zero values. Before 2026-10-25 the counters started at zero and the generated line
with the pointer, the tally and the phrase ran past column 72, so those three were not
compared; a planted model error that stores the tally instead of adding it now fails all 60
programs and failed none before. Seeds 1 and 2 agree on all 60 programs, 1 500 statements,
with no exclusions. The hand-written cases in `tools/difftest/unstring_cases/` agree as well.

`STRING` with value delimiters and `POINTER` (`Cobol/Sem/StringInto.lean`) is tested by
`tools/difftest/stringtest.py`. Each random program has 25 statements: 1 to 3 groups of 1 or 2
sources (literals over `AB,; `, alphanumeric and numeric items), each group `DELIMITED BY SIZE`,
by a literal of 1 or 2 characters, by `SPACE` or by a 1-byte item, into an 8-byte item, with an
optional `POINTER` from 0 to 10 (so out-of-range values occur) and both overflow phrases. Seeds
1 to 4 agree on all 140 programs, 3 500 statements. `ALTER`: `tools/difftest/alter_cases/alter1.cob`
(a paragraph altered three times, reached by `PERFORM … THRU` and by `GO TO`) agrees on every
line. On CardDemo's sample data, CBSTM03A and CBSTM03B (pointers, `ALTER`, `STRING`, a static
`CALL`, a two-level table) write the same 7294 records as GnuCOBOL (`examples/carddemo/README.md`).
`tools/evidence/stm_check.sh` also checks the 11 DISPLAY lines of CBSTM03A's control-block walk,
which GnuCOBOL's copy cannot run, against the lines that follow from the constructed address
space (computed from that file by `stm_compare.py`, not by the model), and GnuCOBOL's exit
status against the model's RETURN-CODE (0: neither program sets it).

Intrinsic functions are tested by three generators in `tools/difftest`, with 20 statements per
program and every result displayed. `fntest_num.py` covers `FACTORIAL` of 0 to 28, `SUM` and
`RANGE` of 1 to 5 arguments of mixed scales, sums of `LENGTH` values, and functions on both sides
of an `IF` relation. `fntest_date.py` covers the four integer-date functions on arguments inside
their domains, weighted to month, year and century boundaries and to 1601-01-01 and 9999-12-31,
`DATE-OF-INTEGER` and `DAY-OF-INTEGER` of a shifted `INTEGER-OF-DATE`, and differences of integer
dates. `fntest_alnum.py` moves `UPPER-CASE`, `LOWER-CASE` and `REVERSE` to shorter, equal and
longer receivers, displays them, takes their `LENGTH` and compares them in `IF`; of
`WHEN-COMPILED`, whose value is each system's own compilation time, it compares the length, the
first two characters and the equality with a copy. Seeds 1 and 2 agree on 60 of 60 programs
each for all three (rows V.fn.num, V.fn.date and V.fn.alnum, `.s1` and `.s2`). The version
before 2026-10-27 rejects all 360 programs as unsupported, and planted errors (`RANGE` with its
sign flipped, every century year a leap year (recipes in tools/difftest/fntest_mutants.md), `z`
not upper-cased) fail 59, 33 and 11 of the 60 programs of seed 1.

`PERFORM VARYING … AFTER` and alphanumeric-edited items are tested by `aftertest.py` and
`aetest.py` in `tools/difftest`. `aftertest.py` runs 6 `PERFORM` statements per program with two
or three levels, inline and out of line, `WITH TEST BEFORE` and `AFTER`, `FROM` and `BY`
operands that read other levels' variables and `UNTIL` conditions on any level, and displays the
variables in every iteration and after each loop; it leaves out the three-level `TEST BEFORE`
case where GnuCOBOL sets the third variable later than IBM documents (`G-after3`). `aetest.py`
runs 25 `MOVE` and `INITIALIZE` statements per program into alphanumeric-edited items (senders
of every category, several receivers, table elements, group members, reference modification, a
data-name subscript, `REVERSE` and `LOWER-CASE`) and displays and compares every result. Seeds 1
and 2 agree on 60 of 60 programs each for both (rows V.after and V.ae, `.s1` and `.s2`); the
version before 2026-10-27 fails all 240 programs (`AFTER` unsupported, the `PICTURE` rejected).

`INITIALIZE` is tested by `inittest.py` in `tools/difftest`. Its 20 statements per program
initialize reference-modified identifiers (alphanumeric, alphabetic, numeric, numeric-edited,
alphanumeric-edited and group items and table elements, literal or data-name positions, with and
without a length), identifiers with a `REDEFINES` clause (elementary and group, levels 01 and
05, a table element, an item inside a redefining group), items under a redefining item and
plain items, one to three per statement; after each statement every record is displayed through
alphanumeric views (GnuCOBOL shows a space digit of a numeric item as `0`) and compared. Seeds 1
and 2 agree on 60 of 60 programs each (rows V.init.s1 and V.init.s2). The version before
2026-10-27 initialized the whole item of a reference-modified identifier and skipped an
identifier with a `REDEFINES` clause: it fails all 120 programs. With the current front end it
fails all 60 programs of seed 1 for either form alone, and agrees on plain items and items under
a redefining item. Planted faults (`tools/difftest/inittest_mutants.md`) fail 53 to 60 programs
per seed, the front-end one 36 and 39.

The key clauses of indexed files, reference modifiers, switches and `INITIALIZE … REPLACING` are
tested by four generators in `tools/difftest`. `reckeytest.py` writes the key clauses of
`filetest.py`'s programs in every spelling IBM allows (`RECORD [KEY] [IS] k`, `ALTERNATE
[RECORD] [KEY] [IS] a`). `rmexprtest.py` runs 25 statements per program on substrings whose
modifiers are integer arithmetic on literals and at most one integer item. `swtest.py` declares
one to four of `UPSI-0` to `UPSI-7` in random spellings, tests their condition names with `IF`,
`NOT`, `AND`, `OR` and `EVALUATE`, and sets them with `SET … TO ON`/`OFF`; the switches start in
random states, given to GnuCOBOL as `COB_SWITCH_n` and to the front end in the same environment
or by `--switch` against the opposite environment. `initrepltest.py` runs `INITIALIZE …
REPLACING` of one to five categories, plain `INITIALIZE`, and pairs that check that `INITIALIZE
X` and `INITIALIZE X REPLACING` every category `BY` `SPACES` or `ZERO` leave the same bytes, on
groups with `FILLER` items, a `REDEFINES` child, a table and items of every category, and
compares the whole storage. Seeds 1 and 2 agree on 60 of 60 programs each for all four (rows
V.reckey, V.rmexpr, V.sw and V.initrepl, `.s1` and `.s2`). The version before 2026-10-27 agrees
on 18 and 25 of the key-clause programs and on none of the others, and planted errors (a key
clause without `KEY` naming the alternate key; `-` read as `+` in a modifier; `SET … TO ON`
storing off; a `REDEFINES` child initialized; an alphabetic item taken as alphanumeric) fail 16,
60, 54, 44 and 37 of the 60 programs of seed 1. `initrepltest.py` leaves out two GnuCOBOL 3.2
deviations from IBM's rule that `FILLER` items and items that cannot receive a `MOVE` are
skipped: GnuCOBOL initializes `FILLER` items with a separate sign (G-fillersep,
`initrepl_cases/fil2.cob`) and index data items (G-initindex). Hand-written cases agree as well:
`value_cases/vallzero1.cob` (`VALUE ALL ZERO` on numeric items of every usage and in a level 88),
`refmod_cases/rmconst1.cob`, and `switch_checks.sh` on `switch_cases/` (the IBM profile,
GnuCOBOL's `SWITCH-n` names against GnuCOBOL `-std=cobol85`, qualification by the mnemonic
name, option errors, linking); `initrepl_checks.sh` checks the unsupported `INITIALIZE` forms.
`initptrtest.py` runs plain `INITIALIZE`, `REPLACING` and plain / `REPLACING` pairs on groups
with `POINTER` items whose bytes are preset, and compares each program with its twin that has a
`FILLER PIC X(4)` for each pointer (the same layout, likewise not initialized), and the twin with
GnuCOBOL, whose pointers are 8 bytes long: seeds 1 and 2 agree on 60 of 60 programs each (rows
V.initptr), while the earlier front end, which let the resolver set the pointers to zero, agrees
on 6 and 3, and planted errors (the pointers in the `MOVE`s; alphanumeric-edited items not
edited there) fail 57 and 32 of the 60 programs of seed 1. `initptr_checks.sh` checks
`initrepl_cases/ptr*.cob` against the lines IBM's rule gives (row V.ptrchk).
In the NIST suite IX108A, IX104A, NC201A, NC211A, NC223A and NC224A pass, and IX103A and IX203A
pass in their groups; before, the front end crashed on IX108A, the resolver rejected the other
IX programs as indexed files without a key, and the NC programs were unsupported. NC211A passes
with the reference run's switch settings (`COB_SWITCH_1=ON`, `COB_SWITCH_2=OFF`).

Index data items (`USAGE INDEX`) and index names are tested by `tools/difftest/indextest.py`
(rows V.ix.s1, V.ix.s2 and V.ix.mixed). Each random program has tables with element lengths 1 to
4 and index data items: 77-level items, the items of a `USAGE INDEX` group, an item inside a
record between two fields, the same layout in a second record, and a table of index data items.
It runs 20 steps:
- `SET` of index names and of index data items (also elements of the table), `SET … UP BY` and
  `DOWN BY`;
- comparisons of index data items with index names and with each other, with every relational
  operator and abbreviated combined relations;
- table elements through index names;
- `SEARCH … VARYING` an index data item;
- `PERFORM VARYING` index names: inline and out of line, `TEST BEFORE` and `AFTER`, `FROM` an
  index name or an integer item, with an `AFTER` level;
- a group `MOVE` between the two records;
- `INITIALIZE` of groups holding index data items;
- `LENGTH OF`, and a `REDEFINES` view of the field after an index data item (its 4 bytes place
  that field).

Every index value is displayed after each change. Seeds 1 and 2 agree on 60 of 60 programs each.
With `--mixed` (seed 3), one step per program moves a value between an index data item and an
index name of another element length. In all 60 programs the model stops with `unsupported` at
the first statement that touches the items involved, and agrees with GnuCOBOL before that. The
version before 2026-10-27 rejects all 120 programs (`USAGE INDEX` unsupported). Three planted errors
are caught (recipes in `tools/difftest/indextest_mutants.md`):
- the `AT END` of a `SEARCH … VARYING` an index data item not setting the item: 32 of the 60
  programs of seed 1 fail;
- `PERFORM VARYING` an index name stepping down: 52 of 60 fail;
- no element-length classes: all 60 `--mixed` programs fail.

Left out of generation are reads of an index data item before its first `SET` (GnuCOBOL gives 0,
the model stops) and the two GnuCOBOL departures listed above. `tools/difftest/index_cases/` holds
three hand-written cases: the layout and `INITIALIZE` (`ix_layout_init.cob`), a read before `SET`
(`u_ix_unset.cob`), and GnuCOBOL's `INITIALIZE` (`g_initindex.cob`). Of the NIST programs blocked by
`USAGE INDEX` or `PERFORM VARYING` an index name, NC131A, NC133A, NC135A, NC206A, NC236A, NC241A and
NC243A now pass. IC106A and IC207A stay unsupported (`CALL … USING` an index data item).

`PROGRAM COLLATING SEQUENCE`, `ALPHABET` and the functions of the collating sequence are tested by
`tools/difftest/colltest.py` (rows V.coll.s1 and V.coll.s2). Most of its random programs name an
`ALPHABET` of literals: strings, `THROUGH` ranges either way, `ALSO` groups, the figurative
constants `HIGH-VALUE`, `LOW-VALUE`, `SPACE`, `QUOTE` and `ZERO`, or ordinal numbers. The others are
in native order: no `PROGRAM COLLATING SEQUENCE` (some with an unused `ALPHABET`), or `NATIVE`,
`STANDARD-1` or `STANDARD-2`. The 20 statements of a program display relation conditions between
items of different lengths, reference-modified items, a group, literals, figurative constants and
an unsigned numeric item; level-88 values and `THRU` ranges, `EVALUATE … THRU`, serial `SEARCH` and
`PERFORM … UNTIL` conditions; `MOVE` and `VALUE` of `HIGH-VALUE` and `LOW-VALUE`; alphanumeric `MAX`,
`MIN`, `ORD-MAX` and `ORD-MIN`, also of arguments that compare equal but differ (so that the
leftmost one shows); numeric `ORD-MAX` and `ORD-MIN`; `INSPECT` of characters that share a position
(it matches characters, not positions); and `ORD` and `CHAR` in the programs of native order. Seeds
1 and 2 agree on 60 of 60 programs each (41 and 46 of them name an alphabet of literals). The
version before 2026-10-27 rejects all 120 programs as unsupported, and five planted errors
(`tools/difftest/colltest_mutants.md`: comparisons in native order, `LOW-VALUE` as X'00', `ALSO` read
as a new position by the front end, a `MAX` tie returning the right argument, the characters the
alphabet leaves out placed first) fail 39, 39, 27, 29 and 39 of the 60 programs of seed 1.
Hand-written cases (`tools/difftest/coll_cases/`, `colltest.py --run`, row V.coll.hand) agree on
every line, among them NC219A's alphabet with `HIGH-VALUE` and `LOW-VALUE` in `VALUE`, `MOVE`,
`DISPLAY` and level 88, and indexed-file keys in binary order. Two GnuCOBOL 3.2 departures are left
out of generation (row V.coll.gdep): `=` and `<>` between two literals ignore `ALSO` (G-alsolit,
`g_alsolit.cob`), and `ORD` and `CHAR` use the native order under an `ALPHABET` of literals
(G-ordchar, `g_ordchar.cob`). `ACCEPT … FROM DAY`, `DAY YYYYDDD` and `DAY-OF-WEEK` are checked by
`tools/difftest/acceptday_check.sh` (row V.acceptday): GnuCOBOL's values agree with its `DATE
YYYYMMDD`, and the model's values at four clock readings are those `date(1)` gives. In the NIST suite
IF105A, IF119A, IF123A, IF127A, IF128A, IF129A, NC214M, NC219A and NC114M pass, where they were
unsupported before, and so do IX210A, IX214A and IX215A, which also need `START` by an alternate key.

`SPECIAL-NAMES CLASS` and class conditions with a class name are tested by
`tools/difftest/classtest.py` (rows V.class.s1 and V.class.s2). Each random program declares two to
four classes: alphanumeric and hexadecimal literals, `THROUGH` ranges in either order (of
characters, hexadecimal literals or ordinal positions), ordinal positions, and `SPACE`, `ZERO`,
`QUOTE`, `HIGH-VALUE` and `LOW-VALUE`; a quarter of the programs name `PROGRAM COLLATING SEQUENCE`
`NATIVE` or `STANDARD-1`. Its 20 steps move data into the items, often only characters of one class,
and test the classes, with and without `NOT`, on alphanumeric and alphabetic items, unsigned and
signed numeric `DISPLAY` items (an embedded sign and a separate leading sign, whose bytes are
characters of the item), a numeric-edited item, a group and its members, table elements with a
literal or a data-name subscript, and reference modifications; also combined with `AND`, `OR`,
`NUMERIC`, `ALPHABETIC` and relations, in `IF`, `EVALUATE TRUE` and `PERFORM … UNTIL`. Seeds 1 and 2
agree on 60 of 60 programs each (381 and 321 conditions true, 540 and 570 false). The version before
2026-10-27 rejects all 120 programs, and planted errors (`tools/difftest/class_mutants.md`:
`THROUGH` without its upper character, a range tested by its lower bound only) fail 7 and 46 of the
60 programs of seed 1. Hand-written cases (`tools/difftest/class_cases/`, `classtest.py --run`, row
V.class.hand) agree on every line, among them NC174A's classes and classes under `PROGRAM COLLATING
SEQUENCE NATIVE`; four more show the class conditions the front end makes unsupported (row
V.class.unsup). In the NIST suite NC174A and NC254A pass, where they were unsupported before.

`DECIMAL-POINT IS COMMA`, `CURRENCY SIGN` and `BLANK WHEN ZERO` on numeric items are tested by
`tools/difftest/dpctest.py` (rows V.dpc.s1 and V.dpc.s2). Its programs declare `DECIMAL-POINT IS
COMMA`, a one-letter `CURRENCY SIGN`, both or neither, and eight numeric-edited items with random
pictures written in the program's roles: a fixed `$`, `+` or `-`, zero suppression with `Z` or `*`,
floating `$`, `+` and `-` strings, the insertion symbols `,` `B` `0` `/`, a decimal point or `V`, a
trailing `+`, `-`, `CR` or `DB`, `BLANK WHEN ZERO` and repetition factors. Its 20 steps move literals
with decimal places (`1234,56`, `,5`) and items into the edited items, compute into them with
`COMPUTE` and `ADD … GIVING`, move `ZERO`, compare with decimal literals, and move integers to an
unsigned numeric item with `BLANK WHEN ZERO`; `VALUE` clauses use decimal literals too. Seeds 1 and
2 agree on 60 of 60 programs each. The version before 2026-10-27 accepts none of the 120 programs
(the front end rejected `DECIMAL-POINT IS COMMA` and made the others unsupported), and four planted
errors (`class_mutants.md`: `,5` read as 5, the decimal point and comma written with their standard
characters, `BLANK WHEN ZERO` on numeric items dropped, `Edit.classify` not skipping `ESym.chars`)
fail 12, 47, 32 and 44 of the 60 programs of seed 1. Hand-written cases (`tools/difftest/dpc_cases/`,
`dpctest.py --run`, row V.dpc.hand) agree on every line, among them NC107A's pictures. Left out of
generation, shown there and listed above: G-ins0, G-floatcs and G-bwzv (row V.dpc.gdep, with
`DISPLAY` of a decimal literal under `DECIMAL-POINT IS COMMA`, which the front end makes
unsupported). GnuCOBOL 3.2 cannot serve as a reference for `CURRENCY SIGN … WITH PICTURE SYMBOL`
(it writes the symbol, not the sign value) or for several `CURRENCY SIGN` clauses (it rejects valid
pictures then), both unsupported in the front end, and it reads `L` as its own variable-length
`PICTURE` symbol even when `L` is the currency sign, so the tester does not use `L`. In the NIST suite
SM103A, SM104A (which checks SM103A's output file), NC108M and NC134A pass, where they were
unsupported (SM104A failed after SM103A); NC107A passes 177 of its 177 tests (175 before a group
moved to a `JUSTIFIED` item was right-justified, below).

`OCCURS DEPENDING ON` is tested by `tools/difftest/odotest.py` (rows V.odo.s1, V.odo.s2 and
V.odo.mixed) against GnuCOBOL `-std=ibm -fno-odoslide`. Each random program has two tables, one
whose object is a record of its own and one whose object lies in the table's group, and some
have a sequential file whose record holds such a table. Its 20 steps move values into the
objects, move the groups to and from other items and each other, write and read elements below
and above the object, compare, `INSPECT`, `STRING`, `UNSTRING` and display the groups and their
substrings, run `SEARCH` and `SEARCH ALL`, loop over the current occurrences, and write and read
variable-length records; after each step both groups are displayed whole. Seeds 1 and 2 agree on
60 of 60 programs each. With `--mixed`, one step per program sets an object outside its range and
references its table: at seed 3 the model stops there with a range fault in all 60 programs and
agrees with GnuCOBOL before. The version before 2026-10-27 rejects all 120 programs, and four
planted errors (`tools/difftest/odotest_mutants.md`: groups always at their maximum length,
`MOVE` without the maximum length rule, no range check, `SEARCH` over integer-2 occurrences) fail
46, 28, 60 and 17 of 60 programs. GnuCOBOL 3.2 departs from IBM in four cases, left out of
generation and shown by `tools/difftest/odo_cases/` (`odotest.py --run`): `STRING … INTO` and
`UNSTRING … INTO` a group that contains its object fill its current length, where IBM's maximum
length rule gives the maximum (G-odostring, G-odounstring); `INITIALIZE` of such a group sets
its current occurrences, which IBM does not allow (G-odoinit; unsupported in the model); and with
`-std=ibm` alone (`odoslide`) GnuCOBOL drops the maximum length rule for `MOVE` too and takes a
reference modification without a length to the group's maximum length (G-odoslide). The
`v_odo_*.cob` cases there agree on every line. In the NIST suite NC235A, NC247A and SQ214A pass,
where the front end rejected them; NC401M, which also uses `RENAMES` and `CORRESPONDING`, is
unsupported for `SYMBOLIC CHARACTERS`, and IC207A stops at `CALL … USING` an index data item.
CardDemo's CSUTLDTC now goes through the front end and the
resolver with no unsupported statement; run alone it stops at `CALL 'CEEDAYS'`, a Language
Environment service the environment does not provide.

`CORRESPONDING` and level-66 `RENAMES` are tested by `tools/difftest/corrtest.py` (rows V.corr.s1,
V.corr.s2). Each random program has a record of random groups (alphanumeric, numeric `DISPLAY`
and `COMP-3`, numeric-edited and index data items, `FILLER`, `OCCURS` and `REDEFINES` items),
two records and a table element derived from it by dropping, adding, renaming, retyping and
reordering items, making them `FILLER` or `OCCURS`, turning groups into elementary items and back
and moving items one group level down, so that the pairs of two groups vary widely, and a record
followed by level-66 entries (an elementary item, a group and `THROUGH` ranges, some operands
qualified). Its 12 steps run `MOVE`, `ADD` and `SUBTRACT CORRESPONDING` between records, groups of
one name and table elements (literal and data-name subscripts), `ADD` and `SUBTRACT` with and
without `ROUNDED`, `ON SIZE ERROR` alone or with `NOT ON SIZE ERROR`, then display every
elementary item of the receiver, or write a level-66 item (`MOVE`, `ADD … ON SIZE ERROR`), read
it (`MOVE`, comparisons) and display it and its record. Numeric items are displayed as the sign
of a comparison with zero and their absolute value. Seeds 1 and 2 agree on 60 of 60 programs
each (335 and 360 pairs; 52 and 38 size errors). The tree without this support rejects 54 of the
seed-1 programs (`RENAMES`) and stops at the first `CORRESPONDING` statement in the other 6, and
three planted errors (`tools/difftest/corrtest_mutants.md`: `REDEFINES` items paired, no size
error trap, a `THROUGH` area as long as `data-name-3`) fail 4, 26 and 26 of 60 programs. The
GnuCOBOL departures listed above (C1, G-corrindex, G-renusage, G-corrmove) are left out of
generation and shown by `tools/difftest/corr_cases/` (`corrtest.py --run`),
whose `v_*.cob` cases agree on every line. In the NIST suite NC207A, NC208A and NC209A pass, where
the front end rejected them or stopped at `CORRESPONDING`; NC202A and NC253A fail only the three
tests of cause C1 (`ADD`/`SUBTRACT CORRESPONDING … NOT ON SIZE ERROR` alone); NC222A passes 8 of
8, its two de-editing `MOVE`s after the `MOVE CORRESPONDING` tests included; NC252A passes its
18 `RENAMES` tests and stops at a `COMPUTE` with an exponent that is not a small integer
literal.

`COPY … REPLACING`, `COPY … OF/IN` and `REPLACE` are tested by `tools/difftest/copyrepltest.py`
(rows V.crepl.s1 and V.crepl.s2) against GnuCOBOL `-std=ibm` with the copybooks next to each
program. A program has 2 to 5 units: `:TAG:` and `(TAG)` placeholders glued to the text on either
side (`:TAG:-A`, `S-:TAG:`, `M-(TAG)-N`), also a copybook copied twice with two tags as CardDemo
copies `CSSETATY`, and a `REPLACE` statement around a `COPY`; `LEADING` and `TRAILING` partial
words, whole words and lower case; literal and numeric operands and operands that must not match
(the other quotation mark, `07` for `7`); qualified and subscripted identifiers as operands;
pseudo-text of several words across lines, with comment lines in the copybook and in the `COPY`
statement and separator commas between words; pictures and level numbers (`==5==` inside
`X(5)`); `REPLACE` in the `PROCEDURE DIVISION` across line breaks, a second `REPLACE` replacing
the first, `REPLACE OFF`; `COPY … REPLACING` under `REPLACE` (`COPY` first) and a `REPLACE` match on
copied text; nested `COPY` with the outer or the inner `REPLACING`; `COPY … OF/IN` a library
directory next to a copybook of the same name, `COPY 'name'`, `SUPPRESS`; operand order and no
second comparison of replaced text; and a `COPY` statement inside a statement. Seeds 1 and 2
agree on 60 of 60 programs each. The version before 2026-10-27 fails 58 and 53 of them (`COPY …
OF`, `REPLACE`, operands of more than one token rejected, replacements not glued), and three
planted errors (`tools/difftest/copyrepltest_mutants.md`: no gluing to the text before a match,
`REPLACE` before `COPY`, a `REPLACING` phrase applied before the nested copybooks are expanded)
fail 20, 24 and 6 of the 60 programs of seed 1. IBM's `COPY` examples 2, 3, 5, 6, 7 and 8 and its
`REPLACE` example (with a non-empty partial word, plus `COPY … OF` a library) agree on every line
(`tools/difftest/copyrepl_cases/`, `copyrepltest.py --run`, row V.crepl.hand); IBM's `REPLACE`
example as written makes cobc 3.2 abort, and the model prints the two lines IBM documents. IBM's
examples 7 and 8 disagree on `:TAG:-GROSS-PAY` under `==:TAG:==` and `TRAILING ==GROSS-PAY==`; by
the text-word rules (`-GROSS-PAY` is a text word of its own) it becomes `PAY7-NET-PAY`, as in
example 8 and in GnuCOBOL. The GnuCOBOL departures listed above are left out of generation and
shown by `g_*.cob` there (row V.crepl.gdep). In the NIST suite SM201A, SM202A, SM206A, SM207A,
SM208A and SM401M pass, where they were unsupported (SM206A's PST-TEST-009 matches across a
debugging line, which the NIST reference compiles with `-fdebugging-line`); in the SM module
SM105A and SM205A stop at sort files (SM103A and SM104A pass since `DECIMAL-POINT IS COMMA` is
modelled).

De-editing, the `MOVE` of a numeric-edited item to a numeric or numeric-edited item, is tested by
`tools/difftest/deedittest.py` (rows V.deedit.s1 and V.deedit.s2). Each random program has three
numeric-edited senders and a table of them, with pictures that use fixed and floating `$`, `+`
and `-`, `CR`, `DB`, `Z`, `*`, the insertion characters `B`, `0`, `/` and `,`, `.` or `V`, and
`BLANK WHEN ZERO`. Each of its 15 steps moves a value into a sender, the sender to one to three
receivers (signed and unsigned numeric items, a COMP-3 item, numeric-edited items, and in some
steps an alphanumeric item or a group), and the value as the sender holds it to twins of the
receivers. The model must agree with GnuCOBOL on every line and give each receiver the content
of its twin, and a program may end with content that no value edits to, where the model must stop
with `invalidData`. Seeds 1 and 2 agree on 60 of 60 programs each (1587 receiver lines, every one
equal to its twin); 38 programs end at such content. The version before 2026-10-27 passes none of
the 120 (it stops with `invalidData` at the first de-editing `MOVE`), and five of six planted
errors (`tools/difftest/deedittest_mutants.md`: the sign lost, the decimal point ignored, no check
of the content, no de-editing, a `0` insertion read as a digit) fail 58, 57, 23, 60 and 24 of 60
programs; the sixth, a negative zero (`-0.00`) faulting, is caught by
`tools/difftest/deedit_cases/v_deedit1.cob`. Where GnuCOBOL's de-editing departs from IBM the
receivers are compared with their twins only: GnuCOBOL ignores a `DB` sign (G-deedit-db,
`deedit_cases/g_deedit_db.cob`: `$ 45.60DB` gives +45.60) and reads a `0` insertion character as
a digit (G-deedit-zero, `g_deedit_zero.cob`: `1230` in `PIC 9(3)0` gives 1230). The tester also
found editing departures, left out of its generation: GnuCOBOL's G-edittrunc (the editing of
literals before truncation above), G-editins, G-editsigncur and G-editfloatsign; and one of the
model, M-editpoint: an insertion character right before the decimal point, after a suppression or
floating string with no `9`, stayed when the integer part was zero (`PIC $$,.99` with 0: the model
gave ` $,.00`, IBM's floating insertion rule and GnuCOBOL `  $.00`), fixed on 2026-10-28 (below).
The hand cases in `tools/difftest/deedit_cases/` (`deedittest.py --run`) agree with GnuCOBOL on
NIST NC222A's two de-editing tests and on edited values set by `VALUE`; `i_valzero.cob` (`VALUE
ZERO` in `ZZ9.99`) and `i_lead0.cob` (an unsuppressed leading zero) stop with `invalidData`. In
the NIST suite only NC222A has de-editing `MOVE`s; it passes 8 of 8 (before this support it
stopped with `invalidData` at the first of them, after its `MOVE CORRESPONDING` tests).
`tests/DeEditSound.lean` proves for every picture, content and configuration that a
de-edited value edits back to the content (`deEdit_sound`); `tests/DeEdit.lean` and
`tests/DeEdit2.lean` check by kernel decision that every value of `PIC -Z9`, `-Z9.9` and
`$$9.9CR` is de-edited back from its editing, NC222A's two cases, and the `invalidData` of
`VALUE ZERO` in `ZZ9.99` (`scripts/lean1.sh`; standard axioms only).

Numeric editing with simple insertion characters around the decimal point and around the string
is tested by `tools/difftest/editpttest.py` (rows V.editpt.s1 and V.editpt.s2). IBM counts an
insertion character (`B`, `0`, `/`, `,`) within or to the immediate right of a zero-suppression or
floating insertion string as part of the string, so with a zero integer part one right before the
decimal point is replaced and a floating symbol goes immediately left of the point (`PIC $$,.99`
with 0 is `  $.00`, `PIC **,.99` with 0.86 is `***.86`), while one left of the string is not part
of it and is written (`PIC 0ZZ.99` with 5.5 is `0 5.50`). Until 2026-10-28 the model kept the
first kind (M-editpoint, above) and replaced the second (M-editlead). Each random program has eight
numeric-edited items whose integer part is a `Z`, `*` or floating `$`, `+` or `-` string, mostly
with no `9`, with insertion characters inside it, right before the point and, in a fifth of the
pictures, left of it, `.` or `V`, places of `9` or of `Z` or `*`, a `0` or `/` right after the
point, fixed signs, `CR`, `DB`, a fixed `$` and `BLANK WHEN ZERO`. Its 20 steps move values, mostly
with a zero integer part, into the items and display them, and some move an item to a numeric item,
which must hold the value the item shows. GnuCOBOL keeps a `0` or `/` in or right after the string
that IBM replaces (G-editins) but edits `,` as IBM does, so an item with such a `0` or `/` has a
twin with `,` in those positions, and the item's editing must be the twin's with its own character
wherever the twin shows `,` (the IBM mirror). Seeds 1 and 2 agree on 60 of 60 programs each (343
and 379 lines of the M-editpoint shape with a zero integer part, 260 and 152 lines of items with a
character left of the string, 350 and 335 lines where GnuCOBOL keeps a `0` or `/` and the model
equals the mirror). The version before both fixes passes 1 of the 120 programs and the version with
the first fix only 43; of seven planted errors (`tools/difftest/editpttest_mutants.md`) the tester
catches six, and the hand cases the seventh, the first fix applied with no integer digit position.
These (`tools/difftest/editpt_cases/v_editpt1.cob` and `v_editlead.cob`, `editpttest.py --run`, row
V.editpt.hand) agree with GnuCOBOL on all 48 lines, the pictures of the theorem programs among them;
`g_editins_pt.cob` and `g_editptb.cob` show G-editins and G-editptb (row V.editpt.gdep), the latter
left out of generation. No picture of the theorem programs, of CardDemo or of the NIST suite has
either shape. In the NIST suite (modules IC, IF, IX, NC, SM and SQ, 309 programs) neither fix
changes an outcome or an output of the model (a time of day in NC214M's report aside).
`tests/EditPoint.lean` proves that the fixed editing equals the old one for every
configuration, `BLANK WHEN ZERO`, value and scale on every picture without the changed cases, in
particular on the four pictures of the theorem programs (`minus_all`, `plus_all`, `z_all`,
`nine_all`), and checks that IBM's content `  $.00` of `PIC $$,.99` now de-edits to 0 (before the
fix it faulted with `invalidData`).

`MOVE` into `JUSTIFIED RIGHT` items is tested by `tools/difftest/justtest.py` (rows V.just.s1 and
V.just.s2). IBM treats a group move "as though it were an alphanumeric-to-alphanumeric elementary
move", and the alignment rules of an alphanumeric receiver are "modified as described in JUSTIFIED
clause", so a group moved to a `JUSTIFIED` item is right-justified and loses its leftmost characters
when it is longer; until 2026-10-28 the model's group `MOVE` filled such an item from the left. A
group receiver is still filled from the left, whatever `JUSTIFIED` members it has. Each random
program has three groups of alphanumeric and numeric members, `JUSTIFIED` items of `PIC X(n)` and
`PIC A(n)`, a table of `JUSTIFIED` elements, a group with a `JUSTIFIED` member and a plain
alphanumeric item; its 20 steps move literals into the members, a group to one to three receivers,
or another sender (a reference modification of a group, a member, a literal, a figurative constant)
to a `JUSTIFIED` item, and display every receiver. Seeds 1 and 2 agree on 60 of 60 programs each
(886 and 843 group moves into `JUSTIFIED` items). The version before the change fails all 120, and
three planted errors (`tools/difftest/justtest_mutants.md`: every alphanumeric receiver of a group
right-justified, no justification, the leftmost characters kept) fail 54, 60 and 59 of the 60
programs of seed 1. The hand case (`tools/difftest/just_cases/v_just1.cob`, `justtest.py --run`, row
V.just.hand) agrees with GnuCOBOL on all 17 lines. No theorem program has a `JUSTIFIED` item. In
the NIST suite the only group moves into one are NC107A's JUST-TEST-04, and NC107A passes 177 of
177 (before, 175); every other outcome is the same.

`DISPLAY` with numeric literal operands is tested by `tools/difftest/displittest.py` (rows
V.displit.s1 and V.displit.s2). IBM's `DISPLAY` takes "any literal", a numeric literal's decimal
point "is treated as an assumed decimal point (that is, as not taking up a character position in the
literal)", and its size "is equal to the number of digits specified by the user"; so an unsigned
literal shows its digits as written (`1.5` as `15`, `0.05` as `005`, `.5` as `5`), as GnuCOBOL 3.2
writes it. Until 2026-10-28 the model wrote the decimal point (`1.5`, `0.05`, `0.5`). IBM gives no
form for a sign, so the front end makes a `DISPLAY` of a signed numeric literal unsupported
(GnuCOBOL writes `-15` and `+15`). Each random program has a few alphanumeric and numeric items; its
15 steps display one to four operands among alphanumeric literals, unsigned numeric literals
(integers and decimals, with leading and trailing zeros and a leading point, up to 18 digits), the
items, `ZERO` and `SPACE`, and a quarter of the programs also display a signed literal, which the
front end must report. Seeds 1 and 2 agree on 60 of 60 programs each (772 and 762 decimal literals;
13 and 12 programs reported). The version before the change fails all 120, and two planted errors
(`tools/difftest/displittest_mutants.md`: leading zeros dropped, a `-` literal not reported by the
front end) fail 46 and 6 of the 60 programs of seed 1. The hand cases (`tools/difftest/displit_cases/`,
`displittest.py --run`) agree with GnuCOBOL on all 12 lines of `v_displit1.cob` (row V.displit.hand),
and the front end reports `u_displit_minus.cob` and `u_displit_plus.cob` (row V.displit.unsup). No
theorem program, CardDemo program or NIST program displays a numeric literal with a decimal point or
a sign; the front end's output on the 503 programs of the identity check is unchanged.

PICTURE character-strings that begin with a comma are tested by `tools/difftest/lctest.py` (rows
V.lc.s1 and V.lc.s2). IBM's separator comma is a comma followed by a space, so a comma right after
`PIC` or `PICTURE [IS]` that another character follows begins the character-string: in `PIC ,ZZ9` it
is a simple insertion character left of the string, which is written (`,  5` for 5), and under
`DECIMAL-POINT IS COMMA` it is the decimal point (`PIC ,99`). Until 2026-10-28 the front end took that
comma for a separator and dropped it, so `PIC ,ZZ9` had three positions and `PIC ,99` was `PIC 99`. Each
random program has six numeric-edited items whose pictures begin with a comma followed by `9`s, a `Z`
or `*` string or a floating `$`, `+` or `-` string, with `B` or `,` between positions, `.` or `V` and
places, a trailing sign, `CR` or `DB` and `BLANK WHEN ZERO`, written `PIC`, `PICTURE`, `PIC IS` or
`PICTURE IS`, each with a twin without the comma (a quarter of the twins written `PIC , ...`, a
separator comma, which stays one); a third of the programs are under `DECIMAL-POINT IS COMMA`, with
pictures that begin with the decimal point. Its 20 steps move values into the items and their twins
and display them, and some move an item to a numeric item, which must hold the value. GnuCOBOL writes
a comma that has no digit position on its left as a space (G-editlc), so the line of an item with a
twin must also equal the IBM mirror, the twin's line with the comma in front. Seeds 1 and 2 agree on 60
of 60 programs each (778 and 582 lines where GnuCOBOL writes the space; the 19 and 29 programs under
`DECIMAL-POINT IS COMMA` equal GnuCOBOL on every line). The version before the change fails all 120,
and two planted errors (`tools/difftest/lctest_mutants.md`: the change removed, a comma followed by a
space also starting the string) fail 60 and 36 of the 60 programs of seed 1. The hand cases
(`tools/difftest/lc_cases/v_lc1.cob` and `v_lcsep.cob`, `lctest.py --run`, row V.lc.hand) agree with
GnuCOBOL on all 28 lines, separator commas after `PIC` among them; `g_editlc.cob` shows G-editlc (row
V.lc.gdep). No picture of the theorem programs, of CardDemo or of the NIST suite begins with a comma; the
front end's output on the 503 programs of the identity check is unchanged.

The phrases of `CLOSE` and `OPEN … REVERSED` are tested by `tools/difftest/closetest.py` (rows
V.close.s1 and V.close.s2). IBM's tables of the `CLOSE` statement go by medium, and a disk file is a
non-reel/unit file there: the term reel applies only to tape, `REEL` and `UNIT` are interchangeable,
and `NO REWIND` or `FOR REMOVAL` on a storage device other than tape leaves "a status key value ...
to indicate the file was on a non-reel medium". So `CLOSE … REEL` or `UNIT`, with or without `NO
REWIND` or `FOR REMOVAL`, gives 07 and leaves the file open and positioned where it was (a `REWRITE`
right after it gets 43, since the last I/O statement was not a successful `READ`); `CLOSE … WITH NO
REWIND` closes the file with 07; `CLOSE … WITH LOCK` closes a sequential or indexed file with 00 and
locks it, so that every later `OPEN` of it in the run gets 38; on a file that is not open each
phrase gives 42. (IBM's glossary calls a direct-access volume a unit; read with the tables'
single-volume column, that would make `CLOSE … REEL` on a disk file a volume switch with status 00.
The `CLOSE` statement's own text puts disk files on a non-reel medium, and the model follows it.)
`REVERSED` "does not apply" to a direct-access device and IBM does not say where the `READ`s then
start, so the model runs `OPEN INPUT … REVERSED` as `OPEN INPUT` only when the `OPEN` fails or the
file has at most one record, and stops with `unsupported` otherwise. `REEL`, `UNIT`, `NO REWIND` and
`REVERSED` on an indexed file (IBM: not valid for VSAM files), `REVERSED` after `OUTPUT`, `I-O` or
`EXTEND` and on a variable-length file, and `REEL`, `UNIT` or `NO REWIND` on an absent `OPTIONAL`
file opened `INPUT` (no medium, no status in IBM's tables) are unsupported. Each random program has
one to three sequential files, some without `FILE STATUS` and some `OPTIONAL` and absent, in a third
of the programs an indexed file, all created by a GnuCOBOL setup program, and 12 to 28 `OPEN` (every
mode, and `OPEN INPUT … REVERSED`), `CLOSE` with each phrase in every spelling, `READ`, `WRITE` and
`REWRITE` statements; every statement displays all file statuses and record areas, compared with
GnuCOBOL, and every status of a file with `FILE STATUS` must equal the tester's IBM mirror. Seeds 1
and 2 agree on 60 of 60 programs each. The version before the change fails 117 of the 120 (the other
three have none of the phrases), and 16 planted errors (`tools/difftest/closetest_mutants.md`) fail
the tester, except one, a front end that writes a plain `OPEN INPUT` for `REVERSED`, which gives the
same result on every generated program and which the hand cases catch. The hand cases
(`tools/difftest/close_cases/`, `closetest.py --run`) agree with GnuCOBOL on all 80 lines of
`v_closereel1.cob`, `v_closelock1.cob`, `v_closelock2.cob` (a `USE` declarative run by the 38 of an
`OPEN` after the lock) and `v_openrev1.cob` (row V.close.hand); the eight `u_*.cob` cases are
reported as unsupported (row V.close.unsup). GnuCOBOL departs from IBM on a `CLOSE` of a file closed
`WITH LOCK` (G-lockclose: 00 and the lock lifted for a sequential file, a crash for an indexed one;
IBM 42, and the file stays locked; `g_lockclose_seq.cob`, `g_lockclose_idx.cob`, row V.close.gdep),
which the tester leaves out. It also ignores `REVERSED`, gives 00 and closes the file for `REEL` on
an absent `OPTIONAL` file, and closes an indexed file on `CLOSE … REEL`, cases IBM leaves undefined
or rejects. In the NIST suite SQ109M, SQ110M, SQ123A, SQ124A, SQ211A, SQ215A, IX204A and IX216A
pass, where they were unsupported, and so does SQ303M (an `OPEN INPUT … REVERSED` of an absent file:
both systems stop with status 35); SQ401M, a flagging test of obsolete phrases, now stops at its
`LINAGE` clause; no other outcome changes. No theorem or CardDemo program uses these phrases; the
front end's output changes only for the 17 programs of the identity check that use them.

Powers whose exponent is an integral data item or expression, not a literal, are tested by
`tools/difftest/powtest.py` (rows V.pow.s1 and V.pow.s2). IBM evaluates `op1 ** op2` in fixed point
when op2 is "an integral data-name or variable": "dmax decimal places and 30-dmax ... integer places
are used", the power is moved to an intermediate result of dmax decimal places and, for a negative
exponent, 1 is divided by that result, again to dmax places; zero raised to a negative power is a
size error (Enterprise COBOL Programming Guide, "Fixed-point data and intermediate results" and its
exponentiation example; Language Reference, SIZE ERROR phrases). The model holds such a power in
`Expr.powInt` (`Sem.powIntVal`: the exact power truncated to dmax places, then `1 /` it truncated to
dmax places for a negative exponent); the front end takes this path in a `COMPUTE` without
`ROUNDED` into numeric items and in relation and sign conditions whose operands are all integers,
where the resolver's dmax is IBM's, and keeps every other such power unsupported; `0 ** 0`, an
exponent value beyond 64 and a power of more than 30 digits stop with unsupported. Each random
program sets its operands by `MOVE` before each of 20 steps: a `COMPUTE` of an expression with one
or two such powers (bases: integer and decimal items, literals, sums, products, negations and a
nested power; exponents: `DISPLAY`, `COMP-3` and `COMP` items, their sums with a literal,
differences, negations and doubles) into a receiver with 0 to 4 places, mostly with `ON SIZE
ERROR`, or an `IF` relation or sign condition with integer operands. Every model line equals
GnuCOBOL's line for an IBM mirror program, in which every such power is replaced by its IBM value
computed by the tester, and equals GnuCOBOL's own line except in three classes where GnuCOBOL
computes the power exactly (G-powtrunc, G-pownegdiv, G-pow0neg, above); a quarter of the programs
end with a power the front end must keep unsupported. Seeds 1 and 2 pass 60 of 60 programs each
(1244 and 1278 lines; 19 and 17 programs reported). The version before the change fails all 120,
and ten planted errors (`tools/difftest/powtest_mutants.md`) fail the tester or a hand-case row.
The hand cases (`tools/difftest/pow_cases/`, `powtest.py --run`) agree with GnuCOBOL on all 21
lines of `v_pow1.cob` (row V.pow.hand), show the departures (row V.pow.gdep) and the unsupported
forms (row V.pow.unsup). No theorem program or CardDemo program has such a power; the front end's
output on the other 501 programs of the identity check is unchanged. In the NIST suite NC252A now
passes 75 of 75, and NC250A runs its exponents and passes 115 of 115 (its IF--TEST-28, a level-88
condition with a `VALUE ALL` literal, passes since the correction described below).

IBM's rules for `dmax` and the places of a quotient, and level-88 `VALUE ALL` literals, are tested
by `tools/difftest/dmaxtest.py` (rows V.dmax.<part>.s1 and .s2), one part per rule. IBM (Enterprise
COBOL 6.4 Programming Guide, "Terminology used for intermediate results", "Fixed-point data and
intermediate results", "Intrinsic functions evaluated in fixed-point arithmetic", "Arithmetic
expressions in nonarithmetic statements"): `dmax` is the largest of "the number of decimal places
needed for the final result field or fields", "the maximum number of decimal places defined for any
operand, except divisors or exponents" and "the outer-dmax for any function operand", and "integer
intrinsic functions return an integer; thus their outer-dmax is always zero"; a quotient carries
"(d2 - d1) or dmax, whichever is greater" decimal places (d2 the dividend's, d1 the divisor's; with
`ROUNDED` "one more decimal place might be carried"); "in an explicit relation condition where at
least one of the comparands is an arithmetic expression, dmax is the maximum number of decimal
places for any operand of either comparand, excluding divisors and exponents", while without a
relational operator (an `EVALUATE` subject or object) "the arithmetic expression is evaluated
without regard to the attributes of its comparand"; an arithmetic expression inside a function
argument takes the function's inner-dmax, the largest of "The number of decimal places defined for
any of its elementary arguments", "The dmax for any of its arithmetic expression arguments" and "The
outer-dmax for any of its embedded functions" (Language Reference, "Function definition and
evaluation": "function evaluation is not affected by operations or operands outside the function";
"Arguments": "The computation of an arithmetic expression that appears as a function argument is
affected by other arguments for that function"). Part all88 (level-88 values with `ALL` literals
next to literals, `THRU` ranges and figurative constants; `IF`, `EVALUATE TRUE`, `SET … TO TRUE`,
relations with `ALL` literals; a fifth of the programs under a `PROGRAM COLLATING SEQUENCE`) checks
every model line and every GnuCOBOL line against the line the tester computes. Part cond (divisions
in relations, sign conditions, abbreviated relations and `EVALUATE` subjects and objects) checks
every model line against the tester's IBM line and every GnuCOBOL line (`-fno-arithmetic-osvs`,
which computes quotients exactly) except where exact quotients give another outcome (G-exactdiv).
Parts edited (numeric-edited receivers), intfn (`INTEGER`, `INTEGER-PART`, `MOD` next to a division)
and div (quotients by IBM's rule: divisors with more places than `dmax`, products as dividends,
nested quotients, two quotients, `ROUNDED`) compare every model line with GnuCOBOL's line for an IBM
mirror program, in which each expression is replaced by its IBM value computed by the tester, and
with GnuCOBOL's own line except in G-exactdiv. So do part fnarg (a quotient inside the arguments of
`MAX`, `MIN`, `SUM`, `RANGE`, `REM`, `ABS`, `INTEGER` and `INTEGER-PART`, nested functions, `MOD` of
such a function, receivers with more places than the arguments) and part rmode (the model's
`ROUNDED MODE`, each COBOL 2014 mode: one quotient as the whole expression into one or two
receivers, a quotient inside a larger expression, `DIVIDE … GIVING` and `DIVIDE … INTO`,
`PROHIBITED` with `ON SIZE ERROR`, where GnuCOBOL raises the size error whenever the quotient has
more places than the receiver, even all zero: G-prohibited); part fncond puts such function
expressions into part cond's conditions and is checked as part cond. Seeds 1 and 2 pass 60 of 60
programs in every part; in part div 366 and 357 of the 1200 steps have a division whose places
differ under the resolver's earlier rule `max(d1, dmax)`, and 87 and 76 store another value under
it; under the rule before the inner-dmax (in a `COMPUTE` the statement's `dmax` and `ROUNDED`
place, in a condition 0) 881 and 926 steps of part fnarg have an argument quotient with other
places and 402 and 394 store another value, and 571 and 599 steps of part fncond have such a
quotient and 275 and 267 an expression with another value; in part rmode 27 and 31 steps store
another value when a lone quotient is rounded from IBM's intermediate. The version before the
corrections fails 120 of 120 programs in parts all88, edited and intfn, 102 in part cond and 112
in part div; the version before the inner-dmax and `ROUNDED MODE` corrections fails 120 of 120 in
part fnarg, 66 in part fncond and 47 in part rmode; twenty-three planted errors
(`tools/difftest/dmaxtest_mutants.md`) fail the tester, a hand-case row, or the resolver check
`tests/DmaxResolve.lean` (the resolvers before the corrections, copied
verbatim: the 15 theorem IRs and the CSUTLDTC and COBSWAIT pinned IRs resolve to the same core IR as
terms, and so do the six NIST IF111A / IF114A paragraphs that divide inside `INTEGER` /
`INTEGER-PART` arguments; of the 395 NIST and 17 CardDemo programs the front end reads, only five
statements resolve differently, the quotients inside `MAX`, `MIN`, `MOD`, `REM` and `SUM` arguments
of IF119A, IF123A, IF124A, IF133A and IF138A, and all five tests still pass). A `COMPUTE`
whose whole expression is one division, with no `ROUNDED` receiver and only numeric receivers,
keeps the earlier scale `max(d1, dmax)`, which stores the same values (a receiver keeps at most
`dmax` places, and truncating to them after truncating to either scale gives the same digits).
CardDemo CBACT04C's interest statement and NIST NC252A's COMP-TEST-32 are the only statements of
the theorem IRs, the 388 NIST programs and the 17 CardDemo programs the front end reads whose
quotient scale would change otherwise, and the resolver gives all of them, except NC250A's
IF--TEST-28, the same core IR as before. The hand cases (`tools/difftest/dmax_cases/`,
`dmaxtest.py --run`) agree with GnuCOBOL on all 60 lines of the `v_*.cob` cases (row V.dmax.hand)
and show GnuCOBOL's departures (row V.dmax.gdep). In the NIST suite the `dmax` corrections change
only NC250A (115 of 115, above); the inner-dmax and `ROUNDED MODE` corrections change no outcome.

Intermediate results that can need more than 30 digits, powers by a literal exponent, powers by the
literal 0 and the composite of operands are tested by `tools/difftest/ir30test.py` (rows V.ir30.s1
and .s2 for part ir30, V.powlit.* for part powlit, V.pow0.* for part pow0, V.c30.* for part c30).
IBM (Enterprise COBOL 6.4 Programming Guide, "Fixed-point data and intermediate results" and
"Truncated intermediate results"; z/OS Language Environment message IGZ0036W) gives an intermediate
result the places "+ or - (i1 or i2) + 1 ... d1 or d2", "* i1 + i2 ... d1 + d2", "/ i2 + d1 ... (d2 -
d1) or dmax"; beyond 30 digits (compatibility mode) it carries "30-d integer and d decimal places"
when d <= dmax, "i integer and 30-i decimal places" when d > dmax and i + dmax <= 30, and "30-dmax
integer and dmax decimal places" otherwise; the decimal places are cut when the program is compiled
("the compiler truncates to 30 ... digits and issues a warning. If truncation occurs at run time, a
message is issued and the program continues running"; IGZ0036W: "some of the truncated digits were
not 0"). The final result of an arithmetic statement with one receiver and no `ROUNDED` is no
intermediate result ("Add ir5 to ir1 yielding Y"); every operation of a condition, a function's steps
and result, and a power are. For a power by a literal exponent n IBM takes d = d1 * n and i = i1 * n
(for a literal base "the number of integers in the value of op1 ** |op2|"); with i + d over 30, or 30
and an even number of digits in the base, it takes the "Same action as when op2 is an integral
data-name or variable": dmax decimal and 30-dmax integer places. The resolver (`Resolve.cap30`)
gives such an intermediate result an `Expr.ir30` node (the value truncated to the carried decimal
places; where IBM cuts a nonzero integer digit and writes IGZ0036W the run stops with unsupported)
and such a power an `Expr.powInt` node; where IBM's text leaves the places open and they decide the
result (`ROUNDED`, with which "one more integer [decimal] place might be carried"; a unary minus,
"Multiplication by -1"; the `dmax` inside a function argument; index names and binary items that can
hold more digits than their PICTURE; `MAX` and `MIN` whose arguments need more than 30 digits
together) the node is `Expr.ir30open`, unsupported when it runs. A `DIVIDE` whose quotient is an
intermediate result (several `GIVING` receivers, `ROUNDED`, `REMAINDER`) and a `MULTIPLY ... ROUNDED`
without `GIVING` whose intermediate result can need more than 30 digits are unsupported; `ADD` and
`SUBTRACT` keep exact results (with a composite of operands of at most 30 digits "no significant
digits are lost"); an expression with a division whose places the front end was given
(`--div-scale`, the GnuCOBOL comparison profile) keeps exact intermediate results. A power by the
literal 0 is `Expr.pow0`: its base is evaluated and its value is 1, and since "If the value of an
expression to be raised to a power is zero, the exponent must have a value greater than zero.
Otherwise, the size error condition exists" (Language Reference, "Arithmetic expressions"), a zero
base is the size error of a `COMPUTE` with `ON SIZE ERROR`, whose imperative runs while "the value of
the resultant identifier affected by the size error is not altered"; without a SIZE ERROR phrase
"The value returned is 1, and a message is issued" ("SIZE ERROR phrases"; the message is not
given), and with `NOT ON SIZE ERROR` alone, which runs only when "a size error condition does not
exist", the run stops with unsupported (the model cannot skip the phrase and store 1). The front
end reports as unsupported an `ADD`, `SUBTRACT`, `MULTIPLY` or `DIVIDE` whose composite of operands,
"a hypothetical data item resulting from aligning the operands at the decimal point and then
superimposing them on one another", exceeds 30 digits ("If the ARITH(COMPAT) compiler option is in
effect, the composite of operands can be a maximum of 30 digits"; for `ADD` and `SUBTRACT` "all
operands in a given statement except those following the word GIVING", for `MULTIPLY` "all
receiving data items", for `DIVIDE` "all receiving data items except the REMAINDER data item";
Language Reference, "Arithmetic statement operands"); a literal counts its digits as written. Part
ir30 draws expressions with intermediate results of 31 to 36 digits (products of 15- to
18-digit items, sums of products, quotients of products, products of quotients, `FUNCTION REM` of
`FUNCTION REM`, `FUNCTION SUM`) for `COMPUTE` with one or two receivers, `IF` relations and `MULTIPLY
... GIVING`; part powlit draws powers of items, literals and sums by exponents around 30 digits,
alone and as operands, for `COMPUTE` and `IF`; part pow0 draws powers by the literal 0 of items that
are 0 in two fifths of the steps, of literals and of expressions, for `COMPUTE` with and without `ON
SIZE ERROR` or with `NOT ON SIZE ERROR` alone (a nonzero base) and `IF`; part c30 draws every form
of the four statements with composites up to 30 digits (30 in about a third of the steps). Parts
ir30 and powlit steer some steps until IBM's cut shows in the receiver or the condition, and about a
third of the programs of each part end with a step the model must stop at (a cut nonzero digit,
open places, a power held with dmax places beyond 30 digits, zero raised to the literal 0 under `NOT
ON SIZE ERROR` alone, a composite over 30 digits). Every model line equals the line of an IBM
mirror program, in which each receiver is set to the value the tester computes by IBM's rules, and
GnuCOBOL's own line except in G-ir30, G-exactdiv, G-powlit, G-litpow64, G-pow00 and G-litpow00.
Seeds 1 and 2 pass 60 of 60 programs in each part (part ir30 1342 and 1394 lines, 23 and 18 programs
ending at a stop; part powlit 1090 and 1053 lines, 12 and 18; part pow0 1232 and 1249 lines, 22 and
20; part c30 1362 and 1375 lines, 20 and 16). The version before the change fails 106 of 120
programs in part ir30, 119 in part powlit, 116 in part pow0 and 36 in part c30 (those that end over
the limit);
twenty-two planted errors (`tools/difftest/ir30test_mutants.md`) fail the tester, a hand-case row or
the resolver check `tests/Ar2Resolve.lean` (the resolver before the change, its `expr` included,
copied verbatim: the 15 theorem IRs and the CSUTLDTC and COBSWAIT pins resolve to the same core IR as
terms; a static bound of every intermediate result's digits under the programs' PICTUREs, the same
in Python, shows that no statement of those 17 programs reaches the new path, the largest bound
being 29). The hand cases (`tools/difftest/ir30_cases/`, `powlit_cases/`, `pow0_cases/`,
`c30_cases/`, `ir30test.py --run`) agree with GnuCOBOL on all 10 lines of `v_ir30_1.cob`, 5 of
`v_powlit_1.cob`, 8 of `v_pow0_1.cob` and 9 of `v_c30_1.cob` (rows V.ir30.hand, V.powlit.hand,
V.pow0.hand, V.c30.hand), show the departures (rows V.ir30.gdep, V.powlit.gdep, V.pow0.gdep) and the
statements the model stops at or the front end reports (rows V.ir30.unsup, V.powlit.unsup,
V.pow0.unsup, V.c30.unsup). No front-end output of NIST, CardDemo or the theorem IRs has a power by the literal 0
or a composite of operands over 30 digits, and the resolver changes only NIST IF133A (its nested
`FUNCTION REM` steps are checked) and NC250A (seven conditions with a power by a data item next to
another operation); in the NIST suite every program of the six modules keeps its outcome,
matches and model output (IF110A 9 of 9, IF133A 17 of 17, NC250A 115 of 115), apart from the date
and time lines of NC214M's `ACCEPT` information, which follow the clock.

`ACCEPT` from the system input device is tested by `tools/difftest/sysintest.py` (rows V.sysin.s1
and V.sysin.s2). Each random program has receivers of every kind IBM allows for this format
(alphanumeric, alphabetic, unsigned numeric `DISPLAY`, a group, table elements with literal and
data-name subscripts, a reference-modified item, a `JUSTIFIED` item, numeric-edited and
alphanumeric-edited items) and COBSWAIT's statements. It fills them with a marker and `ACCEPT`s
them with no `FROM`, `FROM SYSIN`, `FROM SYSIPT` or a mnemonic name of either. The deck has
fixed-length records (LRECL 80 or random: the model's records are the lines padded with spaces,
as in a z/OS card deck) or variable-length ones. A program may end at the end of the input, with a
receiver longer than its record, or with a non-digit card in COBSWAIT's `MOVE`. Every line of the
model equals the IBM rule recomputed by the tester. Every line equals GnuCOBOL's (standard input =
the deck) except those of the five classes above, and the non-digit card stops the model with
`invalidData`. Seeds 1 and 2 pass 60 of 60 programs each (354 and 351 lines). The version before
2026-10-28 rejects all 120 programs. Seven planted errors (`tools/difftest/sysintest_mutants.md`:
padding at the end of the input before any data, one record per `ACCEPT`, the records read not
counted, the right end of a long record kept, no padding after data, `SYSIPT` or the mnemonic names
not recognized) fail 16, 11, 60, 55, 5, 53 and 50 of 60 programs. Hand-written cases
(`tools/difftest/sysin_cases/`, `sysintest.py --run`, row V.sysin.hand) include COBSWAIT's
statements on CardDemo's `WAITSTEP.jcl` card, which agree with GnuCOBOL, and one reproducer per
GnuCOBOL departure. In the NIST suite NC109M was rejected by the front end. The frozen runner gives
it no system input device, so it now stops at its first `ACCEPT` with unsupported. A copy of the
runner that passes its `DATA` block as 80-byte records (`--sysin`) makes it pass, 11 of 11 tests.
NC204M still stops at `DISPLAY UPON` a mnemonic name.

The front-end IR of RECSUM, which now uses the file model, agrees with GnuCOBOL on real
sequential files of 0 to 30 records (`examples/recsum/validate.py --ir`, 40/40). The
validation compares RECSUM's output records; its `WS-COUNT` is counted but never written, so
no run observes it without changing the proved program.

## Trust base

* The Lean kernel, with the axioms `propext`, `Classical.choice` and `Quot.sound`. Each
  example file ends with `#print axioms`.
* Simprocs that evaluate closed terms (`decodeNum` on literal bytes, CP037 tables,
  interval side conditions) only produce `rfl` or `decide` proofs, which the kernel re-checks.
  A compiler bug can make a proof fail, not succeed.
* **`bv_decide`** (used only by `cobol_bv`) checks its LRAT certificate by compiled code. In
  this Lean version that adds one axiom per call (`…._native.bv_decide.ax_N`, visible in
  `#print axioms`), so those theorems also trust the Lean compiler.
* **Not covered by proof, covered by testing:**
  - that the extracted IR matches the COBOL source (the front end is untrusted Python;
    GnuCOBOL validation of its output);
  - that the Lean transcription matches the Java or Rust source (`targettest.py`);
  - that the semantics matches IBM Enterprise COBOL (GnuCOBOL difftests plus the IBM manuals, where GnuCOBOL deviates).

  The COBOL side is now extracted mechanically by `tools/cobolfe`. Mechanical Java and Rust
  extraction (Jimple, Aeneas) lives in the companion project equiv-lean.

## Model and limitations

**Modelled:**
- data:
  - DISPLAY, COMP-3, COMP/BINARY (TRUNC STD/OPT/BIN), COMP-5;
  - signs: trailing/leading overpunch or separate;
  - EBCDIC (CP037) and ASCII;
  - group items, `REDEFINES`, `OCCURS` with subscripts and index names, reference modification
    (each modifier an integer, an integer item plus or minus an integer, or integer arithmetic
    with `+`, `-`, `*` on literals and at most one such item, which the front end evaluates to one
    of the first two), `SYNC` alignment, `VALUE`;
  - `OCCURS [integer-1 TO] integer-2 DEPENDING ON` tables that end their records (IBM, OCCURS
    DEPENDING ON clause). Storage is allocated for integer-2 occurrences. A group containing the
    table has the length of the object's value at the start of the statement (the front end turns
    such a statement into one copy per value of the object, `tools/cobolfe/odo.py`), except where
    IBM's maximum length rule gives the maximum: a receiving group that contains the object, in a
    `MOVE`, `STRING`/`UNSTRING … INTO`, `READ … INTO` or `ACCEPT`, and a `CALL … BY REFERENCE`
    argument. `SEARCH` and `SEARCH ALL` cover the current occurrences. Subscripts go up to
    integer-2, and an occurrence above the object keeps its bytes (IBM leaves its contents
    undefined; GnuCOBOL keeps them). A reference to the table, an item in it or a
    group containing it while the object is outside integer-1 to integer-2 faults with `range`
    (IBM: undefined), a receiving group that contains the object included;
  - de-editing: a numeric-edited item moved to a numeric or numeric-edited item gives its
    unedited value (IBM: "the compiler de-edits the sending data to establish the unedited value
    of the numeric-edited item"): the value whose editing is the item's content, that is the
    digits of its digit positions (a position that suppression, replacement or floating
    insertion filled holds a leading zero), its picture's decimal point and the sign that
    editing shows (`Sem.deEdit` edits the candidate back and compares). Content that no value
    edits to, such as `VALUE ZERO` in a `ZZ9.99` item, a leading zero that a `Z` would suppress
    or a letter, faults with `invalidData` (IBM does not define its unedited value); a negative
    zero (`-0.00`) gives zero. To other receivers a numeric-edited item is alphanumeric;
  - alphanumeric-edited items (`A`, `X`, `9` with the insertion symbols `B`, `0`, `/`): stored as
    alphanumeric; the front end turns a `MOVE` into one into `MOVE`s of its data positions
    (through a hidden item) and of its insertion characters, and makes `INITIALIZE` edit spaces
    the same way (`VALUE` and a group sender are not edited, as IBM specifies);
  - `DECIMAL-POINT IS COMMA` (IBM: it "exchanges the functions of the period and the comma in
    `PICTURE` character-strings and in numeric literals") and one `CURRENCY SIGN` of one character,
    which is then the currency symbol of `PICTURE` strings in place of `$`. The front end reads the
    numeric literals (`1234,56`, `,5`) and the pictures in the standard roles; a numeric-edited
    picture whose decimal point, comma or currency symbol is written with another character starts
    with `ESym.chars`, the bytes that `Edit.edit` writes for them;
  - `BLANK WHEN ZERO` on an unsigned `DISPLAY` numeric item without `P`, which IBM's rule makes
    numeric-edited ("defines the item as category numeric-edited");
  - `USAGE POINTER` (a 4-byte binary item) and `LENGTH OF`;
  - level-66 `RENAMES` entries, by IBM's rules (RENAMES clause): `data-name-2` and `data-name-3`
    are looked up among the items of the entry's level-01 record, and the front end turns each
    entry into a hidden level-01 record that `REDEFINES` its record's storage, with `FILLER` up to
    the renamed area and `data-name-1` over it. Without `THROUGH` and with an elementary
    `data-name-2`, `data-name-1` has `data-name-2`'s description ("All of the data attributes of
    data-name-2 become the data attributes for data-name-1"; not its `VALUE` or level-88 names);
    otherwise it is an alphanumeric group as long as the area, from the first elementary item of
    `data-name-2` to the last one of `data-name-3`. It is qualified only by its record or file
    name;
  - `USAGE INDEX` data items, elementary, in groups and in tables. Each is 4 bytes, as on IBM
    (`LP(32)`) and GnuCOBOL. It holds an occurrence number, as in GnuCOBOL; IBM holds a
    displacement, (occurrence − 1) × element length. The two agree when an index data item meets
    index names of one element length only, and the front end makes the statements touching an
    item that meets several element lengths unsupported. The bytes themselves are not modelled
    (the surface IR makes the item a group of one hidden packed `FILLER`), so a statement that
    would read or write them except through the item is unsupported (see below). A read before
    the first `SET` stops the run (`invalidData`). IBM allows no `VALUE` here, and "If the initial
    value is not explicitly specified, the value is unpredictable"; GnuCOBOL starts at 0;
- statements:
  - `MOVE`, `INITIALIZE` (of items with a `REDEFINES` clause too; a reference-modified
    identifier is one alphanumeric item, as IBM specifies, and receives spaces), and
    `INITIALIZE … REPLACING`, which the front end turns into the `MOVE`s of IBM's rules: each
    item of a named category gets that category's operand, and `FILLER` items, pointers, index
    data items and items under a `REDEFINES` inside the identifier are skipped (the identifier's
    own `REDEFINES` does not count), every table occurrence included. A plain `INITIALIZE` of an
    identifier with a pointer among those items becomes the same `MOVE`s with `SPACE` or `ZERO`
    by category, because the resolver cannot tell a pointer from a 9-digit COMP-5 item and would
    set it to zero;
  - `COMPUTE`, `ADD`, `SUBTRACT`, `MULTIPLY`, `DIVIDE` (with `REMAINDER`, `ROUNDED [MODE]`, `ON SIZE ERROR`);
  - `MOVE`, `ADD` and `SUBTRACT CORRESPONDING`, by IBM's rules (CORRESPONDING phrase). The front
    end pairs the subordinate items of the two groups that have the same name and the same
    qualifiers up to the groups, leaving out `FILLER` and items described with `REDEFINES`,
    `OCCURS`, `USAGE INDEX` or `POINTER` (and the items below them); level-66 items are not
    subordinate items. For `MOVE`, at least one item of a pair is elementary; for `ADD` and
    `SUBTRACT`, both are elementary numeric items. Each pair becomes its own `MOVE`, `ADD` or
    `SUBTRACT` ("The results are the same as if each pair of CORRESPONDING identifiers were
    referenced in a separate MOVE statement"), in the order of the sender's items, with the
    groups' subscripts and `ROUNDED` on each receiver. With `SIZE ERROR` phrases, a hidden counter
    counts the pairs without a size error, a receiver with a size error keeps its value under
    `ON SIZE ERROR`, and the phrase runs once after the last pair (IBM: "the ON SIZE ERROR
    imperative statement is not executed until all the individual additions or subtractions have
    been completed");
  - `IF`, `EVALUATE`;
  - relation, class, sign and level-88 conditions (a level-88 value `ALL literal` is the
    figurative constant: the literal repeated to the size of the conditional variable, also for
    `SET … TO TRUE`). An index data item may be compared with an index name or another index data
    item, without conversion (IBM: any other comparison involving one is undefined);
  - `SET` of condition names, pointers, index names (`TO`, `UP BY`, `DOWN BY`) and index data
    items (`TO` an index name or another index data item, and an index name `TO` one, without
    conversion: the cases IBM allows);
  - switches (`UPSI-0` to `UPSI-7`; with `--profile gnucobol` also `SWITCH-0` to `SWITCH-36`):
    switch-status conditions, also qualified by the mnemonic name, and `SET mnemonic-name … TO
    ON`/`OFF`. The front end gives each switch a hidden one-byte item, `1` when it is on and `0`
    when it is off (IBM: the value tested "is considered to be alphanumeric"), whose start value
    comes from `--switch`, else from `COB_SWITCH_n` (`--profile gnucobol`), else off (IBM's
    default `UPSI(00000000)`). `tools/cobolfe/link.py` refuses to link two programs that use
    the same switch;
  - `PERFORM` (out of line/inline, `THRU`, `TIMES`, `UNTIL` with test before/after, `VARYING`,
    and `VARYING … AFTER …`, which the front end nests by IBM's rules: when an inner level ends,
    the next outer variable is augmented and all inner variables are set to their initial values
    again). A varied index name is set and augmented as by `SET`;
  - `GO TO`, `GO TO … DEPENDING`, `EXIT PERFORM [CYCLE]`, `EXIT PARAGRAPH/SECTION`, `NEXT SENTENCE`;
  - `ALTER` (the front end gives each altered paragraph a hidden switch item and turns its
    `GO TO` into a `GO TO … DEPENDING` on it);
  - `STOP RUN`, `GOBACK`, `EXIT PROGRAM`;
  - `DISPLAY`, `CALL` (to a supplied environment), `CALL 'CEE3ABD'` (abend with its code);
  - static `CALL` of a program linked into the caller's IR (`tools/cobolfe/link.py`; the callee
    may call further linked programs): the arguments are copied into the callee's `LINKAGE`
    items, the callee runs until `GOBACK`, `EXIT PROGRAM` or its end, and they are copied back.
    The callee keeps its storage and open files between calls until a `CANCEL`, which is why
    `LOCAL-STORAGE` in a called program is unsupported;
  - several programs in one source: separately compiled programs in a sequence (a batch, each but
    the last ended by `END PROGRAM`) and the programs they contain (nested programs), which the
    front end links into the first one as `link.py` links a called program
    (`tools/cobolfe/unit.py`). A `CALL` reaches what IBM's rules for program names allow: a
    directly contained program, else a `COMMON` program directly contained in a program that
    contains the caller (unless the caller is in it), else a separately compiled program of the
    source; any other name is outside the source (an environment `CALL`, or `link.py` links it
    later). `CALL identifier` compares the identifier with the name of each program the caller may
    call, as a nonnumeric relation (trailing spaces do not count). A `CALL` of the first program,
    of a program containing the caller or of an active program (one called and not returned:
    hidden flags) is an unsupported recursive `CALL`. `GLOBAL` data items, their condition names
    and indexes, and `FD … GLOBAL` files with their records are names in the contained programs
    unless those declare the name themselves (IBM's search: the program, then the global
    declarations of each containing program outward). Contained programs have no
    `CONFIGURATION SECTION` (IBM), so the `DECIMAL-POINT IS COMMA`, `CURRENCY SIGN` and `CLASS`
    clauses and the mnemonic names (switches, `SYSIN`, `SYSIPT`) of their outermost program
    apply to them; each separately compiled program of the source has its own. All the programs
    of a run unit read one system input device. An `EXTERNAL` record is one storage for all the
    programs of the source that describe it (as a level-01 `REDEFINES` of its first
    description), with any subordinate items but one length and no `VALUE`. `RETURN-CODE` is one
    item per separately compiled program (IBM: implicitly `GLOBAL` in the outermost program),
    and after a `CALL` of another separately compiled program of the source the caller's is set
    to the called program's. `PROGRAM-ID … COMMON`, and `INITIAL` on the main program of the
    run, which has no effect;
  - `CALL … USING BY CONTENT`: the argument's bytes are moved to a hidden item with its
    description (for an alphanumeric literal of n characters `PIC X(n)`, as IBM describes the
    parameter), which is passed instead; `ON EXCEPTION`, `ON OVERFLOW` and `NOT ON EXCEPTION` of a
    program in the run unit, which is always available: the `NOT ON EXCEPTION` statements follow
    the return;
  - `BY REFERENCE` as copy-in/copy-out is IBM's shared storage only when nothing else names the
    arguments' storage while the called program runs. A `CALL` with overlapping arguments, with an
    argument in `GLOBAL` or `EXTERNAL` storage that the called program, a program it may call or a
    `USE GLOBAL` declarative that may run meanwhile names, or with a `LINKAGE` argument while such
    storage is named, is unsupported (`link.py` checks overlapping arguments). The same item passed
    twice is one storage in the called program: a variant of the called program names the second
    parameter through a hidden `REDEFINES` of the first, and only the first is copied in and out;
  - `INITIAL` called programs (every `CALL` enters them in their initial state) and `CANCEL` by
    literal or identifier (the next `CALL` does; a `CANCEL` of an active program is unsupported):
    the program and the programs it contains get their initial state. Every `WORKING-STORAGE`
    record but `EXTERNAL`, `REDEFINES` and switch records (and `RETURN-CODE` only in a separately
    compiled program) gets the bytes of a hidden copy with the same `VALUE` clauses, so items
    without `VALUE` get the copy's initial contents (IBM: undefined), and `PERFORM` and `ALTER`
    states are reset. It is unsupported when a file of those programs may be open, since closing
    it without a status and declaratives is not expressible. For programs linked by `link.py`,
    `PATH.link.json` files next to the linked IRs record which programs each contains; a `CANCEL`
    of a program not linked into the program that cancels it is unsupported;
  - `SET ADDRESS OF item TO p` copies the item's length from the environment's address space at
    `p` (programs that only read such items, like CBSTM03A); `SET p TO q` between pointers;
  - files: `OPEN`/`CLOSE`, sequential `READ`/`WRITE`, indexed files with `ACCESS SEQUENTIAL`,
    `RANDOM` or `DYNAMIC` (keyed `READ` by the record key or an alternate key, `READ NEXT`,
    `WRITE`, `REWRITE`, `DELETE`, `START` by the record key or an alternate key or a leading part
    of either with `=`, `>`, `NOT <`/`>=`), `FILE STATUS` codes
    00/02/05/10/21/22/23/41/42/43/44/46/47/48/49, `AT END`/`INVALID KEY` phrases, abend when an
    error is not handled. After the at-end condition, a failed `START` and, in dynamic access, a
    failed keyed `READ`, `READ NEXT` gives 46 until an `OPEN`, a successful `START` or a
    successful keyed `READ` sets the file position indicator again (IBM's status table: "The
    preceding READ statement was unsuccessful but did not cause an at-end condition"; until
    2026-10-27 a `READ NEXT` after a failed keyed `READ` by the record key continued from the
    earlier position). Initial file contents, `OPEN` outcomes and which `OPTIONAL` files are
    absent come from the environment;
  - alternate record keys, by IBM's rules (START, READ and WRITE statements, file status 02): a
    successful `START` makes the key it names the key of reference of the `READ NEXT`s that
    follow, and so does a keyed `READ` in dynamic access; `OPEN` makes it the record key. Records
    with one value of an alternate key `WITH DUPLICATES` are read "in the order in which they were
    placed in the file" (a `REWRITE` that changes the value places the record again; the records in
    the file before the run come first, in record-key order), and a keyed `READ` by such a key
    gets the first of them. The file position indicator is a place in the key's order, so a
    record deleted there is skipped and a record written after it is read. Status 02: a `READ`
    whose next record has the same value of the key of reference, a `WRITE` or `REWRITE` that
    created a duplicate value (for a `REWRITE`, of a key whose value it changed). These rules run
    only for files whose key of reference can be an alternate key or that have a duplicates key
    (`FileDecl.keyRef`, set by the resolver; `Cobol/Sem/File.lean`); other files keep the
    record-key code;
  - `SAME RECORD AREA`: the records of the files it names share one record area. `SAME AREA` has
    no effect, as IBM's page says first ("syntax checked, but has no effect on the execution of
    the program") and GnuCOBOL does, though the same page also says that for VSAM files it "is
    treated as if equivalent to the SAME RECORD AREA clause";
  - `SELECT OPTIONAL` files, by IBM's table of available and unavailable files (OPEN statement
    notes): an `OPEN` of an absent `OPTIONAL` file gives status 05 and an empty file. `INPUT`
    leaves the file absent, so the first `READ` gives the at-end condition (10) and a keyed `READ`
    or `START` the invalid-key condition (23), and the next `OPEN` gives 05 again; `I-O` and
    `EXTEND` create the file. `OUTPUT` creates it with status 00, as for any file. Which files
    are absent is an input of the run (IBM: a QSAM file whose data set is not there, a VSAM file
    that has never held records);
  - `DECLARATIVES` with `USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE ON` file names or an open
    mode (`Cobol/Sem/Exec.lean`, `ioErr`), by IBM's rules: when an `OPEN`, `CLOSE`, `READ`,
    `WRITE`, `REWRITE`, `DELETE` or `START` ends with a status of 10 or more that no `AT END` /
    `INVALID KEY` phrase handles, the declarative naming the file runs, else the one naming the
    mode the file is open in (for an `OPEN` of a closed file, the mode it is being opened in), as an
    out-of-line `PERFORM` of its section; control then continues with the statement after the
    I/O statement. With no applicable declarative, a file with a `FILE STATUS` item continues and
    one without abends, as before. `tools/cobolfe/link.py` refuses to link a called program with
    declaratives, or a caller with open-mode declaratives, since they would catch the other
    program's files. With several programs in one source the semantics selects among the
    declaratives of all of them, while IBM selects by the program of the I/O statement (its own
    file-specific declarative, its own mode-specific one, then the `USE GLOBAL` ones of each
    containing program outward); the front end makes an I/O statement unsupported when the two
    selections can differ for some open mode (`unit.py`, `check_io`). A declarative section without
    statements gets an empty paragraph;
  - variable-length records (`RECORD VARYING [FROM m] [TO n] DEPENDING ON item`,
    `RECORD CONTAINS m TO n`, or record descriptions of different lengths or with an `OCCURS
    DEPENDING ON` table without a `RECORD` clause, which give the lengths of the shortest, with
    integer-1 occurrences, and the longest): `WRITE` writes as many bytes as the `DEPENDING ON`
    item says, or the named record's length without one (with such a table, its current length:
    IBM, RECORD clause format 3), and a length
    outside `m ..= n` is a boundary violation (status 44). The record area of a file is as long
    as its longest record description. `READ` sets the item to the length read, and
    `READ … INTO` moves only the record read. A sequential `REWRITE` may not change a record's
    length (44);
  - `STRING … DELIMITED BY SIZE` without `POINTER` (static positions, lowered by the front end),
    and `STRING … DELIMITED BY` a value `… INTO r [WITH POINTER p] [ON OVERFLOW …]
    [NOT ON OVERFLOW …]` (`Cobol/Sem/StringInto.lean`);
  - `INSPECT … TALLYING / REPLACING / TALLYING … REPLACING / CONVERTING` with `CHARACTERS`,
    `ALL`, `LEADING`, `FIRST` and `BEFORE / AFTER INITIAL`, following the standard comparison
    cycle (`Cobol/Sem/Inspect.lean`). A signed numeric `DISPLAY` item is inspected as IBM
    specifies, as if moved to an unsigned item of the same length: an embedded sign is removed
    from its byte, and a separate sign byte is neither examined nor replaced. After replacing or
    converting, the item keeps its sign, as in GnuCOBOL (IBM's text leaves this open); a
    replacement that leaves a non-digit in the byte carrying an embedded sign is `unsupported`.
    A phrase with both delimiters where the first `BEFORE` occurrence lies before the end of the
    `AFTER` delimiter is `unsupported`: the standard's wording and GnuCOBOL disagree there, and
    IBM's behaviour could not be checked;
  - serial `SEARCH table [VARYING index | item] [AT END …] WHEN … [END-SEARCH]`. The table's first
    index, or the `VARYING` index when it is one of the table's, runs from its current value to
    the `OCCURS` count. An integer `VARYING` item goes up by one with each step, and an index data
    item by one occurrence;
  - `SEARCH ALL` on tables with `ASCENDING`/`DESCENDING KEY`: the element satisfying the
    `WHEN` condition, or `AT END`. A table out of `KEY` order and several matching elements are
    `unsupported`, because IBM leaves those results unpredictable;
  - `UNSTRING … DELIMITED BY [ALL] d OR … INTO r [DELIMITER IN d] [COUNT IN c] … [WITH POINTER p]
    [TALLYING IN t] [ON OVERFLOW …] [NOT ON OVERFLOW …]` (`Cobol/Sem/Unstring.lean`);
  - `FUNCTION CURRENT-DATE` and `ACCEPT … FROM DATE/TIME` (clock readings from the environment),
    and `ACCEPT … FROM DAY` (YYDDD), `DAY YYYYDDD` and `DAY-OF-WEEK` (1 is Monday), which the front
    end computes from the reading's date with `INTEGER-OF-DATE` in hidden items;
  - `ACCEPT identifier` from the system input device: with no `FROM`, `FROM SYSIN`, `FROM SYSIPT`
    or a mnemonic name that `SPECIAL-NAMES` gives either (a mnemonic name takes precedence over the
    environment name it spells, as IBM specifies). The records come from the environment
    (`Env.sysin`, each with its own length: a z/OS in-stream deck is fixed-length, usually 80
    bytes). IBM format 1: records are read until the receiving area is filled, the last one
    truncated; at the end of the input the area is padded with spaces when some data was read and
    left unchanged when none was (no byte: also after empty variable-length records); the bytes go
    in with no editing or checking (`Sem.sysinRead`). The records read so far are counted in the
    `pos` of the entry `0` of `State.files`, which no declared file uses. Without a system input
    device (`none`; IBM: the `ACCEPT` fails when the ddname is not defined) the statement faults
    with `unsupported`. The receiver is a group or a `DISPLAY` item (the front end rejects others,
    as IBM's compiler does); a group with an `OCCURS DEPENDING ON` table is unsupported;
  - `PROGRAM COLLATING SEQUENCE` naming an `ALPHABET` (`SPECIAL-NAMES`), by IBM's rules. `NATIVE`,
    and `STANDARD-1` or `STANDARD-2` with ASCII data or `EBCDIC` with EBCDIC data, are the native
    order. An `ALPHABET` of literals orders the characters as given (`THROUGH` ranges either way,
    `ALSO` sharing one position, a numeric literal naming the character at that ordinal position,
    `HIGH-VALUE` and `LOW-VALUE` the native ones), then every other character in native order
    (`Resolve.collation`). Nonnumeric relation conditions, level-88 conditions, `EVALUATE`, `SEARCH`
    and alphanumeric `MAX`, `MIN`, `ORD-MAX` and `ORD-MIN` compare by it (`Cond.alnumCmpSeq`, emitted
    only then), and `HIGH-VALUE` and `LOW-VALUE` are its highest and lowest characters (IBM: "the
    last character specified (or defaulted to when any characters are not explicitly
    specified)", "the first character specified"), in `VALUE` too. Indexed-file keys keep their
    binary order (IBM, `RECORD KEY`), and `INSPECT`, `STRING` and `UNSTRING` match characters. The
    resolver rejects an invalid alphabet (a character given twice, numeric and alphanumeric
    literals mixed), as IBM's compiler does;
  - `SPECIAL-NAMES CLASS` and class conditions with a class name (IBM: "identifier-1 consists
    entirely of the characters listed in the definition of class-name"). A class is the set of the
    characters of its literals: every character of an alphanumeric or hexadecimal literal, for a
    numeric literal n the character at ordinal position n of the native order, for `THROUGH` every
    character between the two, in either order. The front end turns `identifier IS [NOT]
    class-name` into comparisons of each byte of the identifier, as a one-byte reference
    modification, with the class's runs of consecutive characters: exact, since one byte is
    compared with one byte in native order;
- intrinsic functions whose results IBM defines exactly (integer functions, and the mixed
  functions it evaluates in fixed point): `ABS`, `INTEGER`, `INTEGER-PART`, `MOD`, `REM`, `MIN`,
  `MAX`, `SUM`, `RANGE`; `ORD`, `CHAR`, `ORD-MAX`, `ORD-MIN`, and `MAX` and `MIN` of alphanumeric
  arguments, by the program collating sequence (the leftmost argument on ties; `CHAR` of a
  position outside the sequence faults with `range`; `CHAR` takes an integer item or literal);
  `FACTORIAL` (arguments 0 to 28) and the integer-date functions
  `INTEGER-OF-DATE`, `DATE-OF-INTEGER`, `INTEGER-OF-DAY`, `DAY-OF-INTEGER` (day 1 is
  1601-01-01; an argument outside a function's domain faults with `range`, where IBM ends the
  run with an error); `LENGTH` of a literal, of an item without reference modification or of an
  alphanumeric function (a compile-time constant); `UPPER-CASE`, `LOWER-CASE` and `REVERSE` of an
  alphanumeric item, literal or function (only the 26 letters change case, as IBM specifies);
  and `WHEN-COMPILED`, which is the time the front end ran (or its `--when-compiled` option);
- IBM's fixed-point rules for intermediate results where they are stated: a quotient keeps
  "(d2 - d1) or dmax, whichever is greater" decimal places (d2 the dividend's, d1 the divisor's; one
  more with `ROUNDED`, a dialect parameter, see the assumption below), truncated; `dmax` is the most
  decimal places of a `COMPUTE`'s receivers (numeric-edited ones included) and of its operands
  outside divisors and exponents, an integer function (`INTEGER`, `INTEGER-PART`, `MOD`,
  `FACTORIAL`, the integer-date functions, `ORD-MAX`, `ORD-MIN`) contributing none; in an explicit
  relation the most decimal places of any operand of either comparand; in a sign condition and for
  an `EVALUATE` subject or object (no relational operator) those of the expression's own operands.
  An arithmetic expression inside a function argument is evaluated with the function's inner-dmax:
  the most decimal places of that function's arguments (elementary arguments, the operands of
  expression arguments outside divisors and exponents, and the outer-dmax of embedded functions; 0
  for `MOD`, `FACTORIAL` and the integer-date functions, whose arguments are integers), in every
  statement; it does not depend on the statement's receivers, on operands outside the function or
  on the `ROUNDED` phrase (Enterprise COBOL 6.4 Language Reference, "Function definition and
  evaluation": "function evaluation is not affected by operations or operands outside the
  function", and "Arguments"; Programming Guide, "Terminology used for intermediate results"). A
  `COMPUTE` whose whole expression is one division, with no `ROUNDED` receiver and only numeric
  receivers, keeps the scale `max(d1, dmax)` of earlier versions, which stores the same values.
  Beyond 30 digits (`ARITH(COMPAT)`) an intermediate result keeps the places IBM's table carries
  ("30-d integer and d decimal places" when d <= dmax, otherwise "i integer and 30-i decimal places"
  or "30-dmax integer and dmax decimal places"), its decimal places cut; a statement's final result
  with one receiver and no `ROUNDED` is none, every operation of a condition is one.
- IBM's limit on the composite of operands of `ADD`, `SUBTRACT`, `MULTIPLY` and `DIVIDE` (at most
  30 digits with ARITH(COMPAT), Language Reference, "Arithmetic statement operands"): the front end
  reports a statement beyond it as unsupported, naming the composite's digits and the limit.
- exponentiation whose exponent is an integral data item or expression (IBM evaluates it in
  fixed point: the power held with `dmax` decimal places, and for a negative exponent 1 divided by
  it, again to `dmax` places), in a `COMPUTE` without `ROUNDED` into numeric items and in relation
  and sign conditions whose operands are all integers; and a power by a literal exponent, exact
  while IBM's exponentiation table carries its places (i + d below 30, or 30 with an odd number of
  digits in the base), otherwise held the same way. A power by the literal 0 evaluates its base and
  is 1; zero raised to it is a size error: in a `COMPUTE` with `ON SIZE ERROR` the imperative runs
  and the receivers keep their values, elsewhere the value is 1 (IBM's message is not given; with
  `NOT ON SIZE ERROR` alone the run stops with unsupported, below).

**Unsupported programs.** The front end never drops a construct that can change behaviour.
These constructs outside the statements make the whole program unsupported (its first statement
faults with `unsupported "program: …"`): the declaratives `USE FOR DEBUGGING` and
`USE BEFORE REPORTING` (only `USE [GLOBAL] AFTER STANDARD EXCEPTION/ERROR PROCEDURE` is
modelled); a `PROGRAM COLLATING SEQUENCE` naming `STANDARD-1` or `STANDARD-2` with EBCDIC data
(where IBM puts the characters outside ASCII is not modelled), `EBCDIC` with ASCII data, or an
alphabet that is not defined, and its `FOR ALPHANUMERIC` / `FOR NATIONAL` forms; the
`SPECIAL-NAMES` clause `SYMBOLIC CHARACTERS`, an `ALPHABET` or `CLASS` clause that does not
parse, and a `CURRENCY SIGN` clause with `PICTURE SYMBOL`, a second one, or a sign that is not
one character IBM allows (or is a lowercase letter: the front end reads `PICTURE` strings in
upper case, and currency symbols are case-sensitive); `WITH DEBUGGING MODE`; a second (VSAM)
`FILE STATUS` item; sort files (`SD`); the `FD` clauses `LINAGE`, `CODE-SET`, `REPORT` and
`EXTERNAL` (each program sharing an external file has its own `FILE STATUS` item, which one file
declaration of the model cannot express); `GLOBAL` on an item that is not level 01, `EXTERNAL`
on one that is not a level-01 `WORKING-STORAGE` item or that has a `REDEFINES` clause, `VALUE`
in an `EXTERNAL` record, and an `EXTERNAL` record described with another length than in an
earlier program of the source, or with index data items in either description (the later program
faults when it is called); a `PROGRAM COLLATING SEQUENCE` of a later program of the source other
than the first program's (and `tools/cobolfe/link.py` refuses to link a program whose sequence
differs from its caller's); `BLANK WHEN ZERO` on an item that is neither numeric-edited nor an
unsigned `DISPLAY` number without `P`, or on such a number with `VALUE ZERO` or a numeric
`VALUE` (IBM: the clause "does not affect initial settings as determined by the VALUE clause";
GnuCOBOL blanks them), `JUSTIFIED` on one that is not alphanumeric, and a `SIGN` clause on one
that is not a signed `DISPLAY` number; an index data item in a file record, in the scope of a
`REDEFINES` or `SYNCHRONIZED`, and `PROCEDURE DIVISION USING` an item holding one;
`PROCEDURE DIVISION USING BY VALUE/CONTENT` and `RETURNING`; `LOCAL-STORAGE` in a called
program; an `OCCURS DEPENDING ON` table followed by other items in its record (variably located
items, IBM's complex ODO), inside another table or containing one, with or in a `REDEFINES` (the
records of one `FD` share their area, which is allowed), or with `VALUE` clauses in it or on a
group containing it; `RECORD CONTAINS n` for a file whose record has such a table; a `GLOBAL`
record with such a table in a program that contains programs, and such a table in a contained
program whose object a containing program declares; and a level-66 entry renaming an index data
item, a pointer or a group containing an `OCCURS DEPENDING ON` table, or a `THROUGH` range whose
first or last elementary item does not start or end the area. The front end rejects
`COPY … OF/IN` a library name that is not a literal (IBM takes it as an environment variable; a
literal names a directory), a second `REPLACING` phrase in a chain of nested `COPY` statements
and a copybook that copies itself (IBM errors), a `REPLACE` or `REPLACING` operand pair without
`BY`, an unknown column-7 indicator, a `>>SOURCE` format switch, an `OCCURS DEPENDING ON` object
that is not an integer item outside every table, an `END PROGRAM` that names another program, a
contained program (or one containing programs) without its `END PROGRAM`, the level-66 entries
IBM does not allow (renaming the level-01 record, an item with or under `OCCURS`, an
`OCCURS DEPENDING ON` table between `data-name-2` and `data-name-3`, a `data-name-3` that starts
or ends before `data-name-2` or lies within it), `CORRESPONDING` operands that are not group
items or are level-66 items or reference-modified, or under which a corresponding name is not
unique, a numeric literal written with a period under `DECIMAL-POINT IS COMMA`, and a `$` in a
`PICTURE` string when a `CURRENCY SIGN` clause names another sign (GnuCOBOL's compiler rejects
both as well).
What it ignores concerns only listings, media or concurrent access: comment entries, `BLOCK
CONTAINS`, `LABEL RECORDS`, `VALUE OF`, `DATA RECORDS`, `RECORDING MODE`, `RESERVE`, `PADDING
CHARACTER`, `RECORD DELIMITER`, `LOCK MODE`, `SHARING`, `READ … WITH NO LOCK`, the other
`I-O-CONTROL` entries, `SYNC` on items other than binary ones, and debugging lines (comments
unless `WITH DEBUGGING MODE` is declared). Mnemonic names other than switches' have no effect
by themselves; `DISPLAY UPON` (other than `SYSOUT`), `ACCEPT FROM` them (other than those of
`SYSIN` and `SYSIPT`) and `WRITE ADVANCING` are unsupported statements.

**Not modelled, or reported as `unsupported`:**
- negative zero;
- recursive `PERFORM` and resuming an abandoned `PERFORM` (implementation-specific on IBM);
- with `OCCURS DEPENDING ON` tables: `INITIALIZE` of a group containing one (IBM does not allow
  it), `LENGTH OF` such a group and its level-88 names, the table's items or such a group in a
  `VARYING` phrase or such a group in an `UNTIL` condition, `SET ADDRESS OF` them, a statement in
  which a receiver stores into an object before a reference that depends on it, and a statement
  whose tables have more than 4096 object values together;
- COMP-1/COMP-2 floating point;
- aliasing through `SET ADDRESS OF`: a write to such an item changes the item only, not the
  address space, and two items placed at one address do not share storage;
- whether a program outside the run unit is available: a `CALL` with `ON EXCEPTION` or `NOT ON
  EXCEPTION` of a program that neither the front end nor `link.py` linked, a `CALL identifier`
  whose value names no linked program, and a `CANCEL` of a program not linked into the program
  that cancels it are unsupported (the environment's programs, `Env.call`, are called without
  those phrases); `CALL … BY VALUE`, `OMITTED`, `RETURNING`, `BY CONTENT` of a numeric literal, a
  figurative constant, a special register or a reference modification without literal positions;
- `RETURN-CODE` after a `CALL` of a program linked by `link.py` or of the environment (not passed
  back; only between programs of one source);
- relative and line-sequential files;
- `OPEN … WITH NO REWIND`; `OPEN … REVERSED` of a file of two or more records (IBM: `REVERSED` does
  not apply to a direct-access device and the order of the `READ`s is not given), of an indexed or a
  variable-length file, or after `OUTPUT`, `I-O` or `EXTEND`; `CLOSE … REEL`, `UNIT` or `NO REWIND`
  of an indexed file (IBM: not valid for VSAM files) or of an absent `OPTIONAL` file opened `INPUT`;
- `SORT`/`MERGE`;
- national and DBCS data;
- `EXEC SQL`/`CICS`;
- index data items:
  - statements that would read or write their bytes other than as index data items: a group
    `MOVE` (except between groups of one length with index data items at the same offsets), a
    group `DISPLAY` or comparison, an item overlaying one through `REDEFINES`, `CALL … USING` and
    `PROCEDURE DIVISION USING`;
  - programs with an index data item in a file record, in the scope of a `REDEFINES`, or
    `SYNCHRONIZED`;
  - statements touching an index data item that meets index names of tables with different
    element lengths;
  - direct references other than in `SET`, `SEARCH … VARYING` and comparisons with index names or
    index data items (IBM allows no others: `MOVE`, `DISPLAY`, arithmetic, subscripts, `PERFORM
    VARYING`, `SET … UP BY`);
- in `PERFORM VARYING … AFTER`: a division in `FROM` or `BY`, and `EXIT PERFORM` in
  an inline body; with an alphanumeric-edited receiver: `MOVE ALL` of a non-figurative literal
  (GnuCOBOL fills the item unedited, the standard edits it), a function or an item with a
  data-name subscript or reference modification sent to several receivers (IBM evaluates the
  sender once), `READ … INTO`, `ACCEPT`, `STRING`/`UNSTRING … INTO`, `DELIMITER IN`,
  `WRITE`/`REWRITE … FROM` and `CURRENT-DATE`; a `MOVE` of such an item onto itself faults as an
  overlap;
- `INITIALIZE` of a reference-modified `COMP`, `COMP-3` or `COMP-5` item (IBM allows reference
  modification of `DISPLAY` items only);
- with `CORRESPONDING`: a `MOVE` pair whose elementary `MOVE` IBM's table does not permit (an
  alphabetic or alphanumeric-edited item to a numeric or numeric-edited one, a numeric item to an
  alphabetic one, a non-integer numeric item to an alphanumeric or alphanumeric-edited one), a
  pair whose bytes are shared with an index data item, operands that may share storage (IBM:
  overlapping operands give unpredictable results) unless they are the same item with the same
  subscripts, a receiver that may share storage with a subscript of either operand, and `SIZE
  ERROR` phrases with no corresponding pair; `INITIALIZE` of a level-66 item;
- `INITIALIZE … WITH FILLER`, `… TO VALUE` and `… THEN TO DEFAULT`; `INITIALIZE` of a pointer;
  `INITIALIZE … REPLACING` of a reference-modified identifier or one with a data-name subscript,
  of an index data item, or `BY` an item with a data-name subscript or reference modification or
  in the storage of an identifier (its value would be read again after earlier `MOVE`s); `SET`
  of a switch-status condition name `TO TRUE` or `FALSE`;
- the intrinsic functions IBM evaluates in floating point (`ACOS`, `ANNUITY`, `ASIN`, `ATAN`,
  `COS`, `LOG`, `LOG10`, `MEAN`, `MEDIAN`, `MIDRANGE`, `NUMVAL`, `NUMVAL-C`, `PRESENT-VALUE`,
  `SIN`, `SQRT`, `STANDARD-DEVIATION`, `TAN`, `VARIANCE`: a long floating-point value under
  ARITH(COMPAT), so for example `MIDRANGE (1 2)` stored into `PIC 9` is 2 on IBM, a floating-point
  result being always rounded; `NUMVAL` and `NUMVAL-C` return "a floating-point approximation",
  `MEAN` and `MIDRANGE` "a numeric value that approximates" the average, and `MEDIAN` of an even
  number of arguments the mean of the two middle ones), `RANDOM`, the others not listed above,
  and `CURRENT-DATE` outside a `MOVE`;
- other exponents: one with decimal places or a division (IBM: floating point), a function
  reference or a power, a negative literal (IBM's rule for literals differs from that for data
  items), and a power with such an exponent under `ROUNDED`, into a numeric-edited item, inside a
  function argument or under a literal exponent, in a `COMPUTE` with `INTEGER` or `INTEGER-PART`
  of an argument with decimal places, or in a condition with an operand with decimal places; at
  run time `0 ** 0` (an exponent that is a data item), an exponent value beyond 64 and a power held
  with `dmax` places of more than 30 digits (by a data item or by a literal) stop with unsupported,
  and so do, under `ROUNDED`, a power by a literal of 28 or more digits (IBM's text leaves its row
  open) and, in a `COMPUTE` with `NOT ON SIZE ERROR` and no `ON SIZE ERROR`, zero raised to the
  literal 0 (the size error skips that phrase while the value 1 is stored);
- intermediate results of more than 30 digits where IBM writes a run-time message (IGZ0036W, a
  cut integer digit that is not 0) or where its text leaves the places open (`ROUNDED`, a unary
  minus, index names, binary items beyond their PICTURE, `MAX` and `MIN` of arguments that need
  more than 30 digits together) or, inside a function argument, where the model's 30-digit
  analysis does not follow the function's inner-dmax (places that depend on the `dmax` range it
  takes there, an argument of `MOD`, `FACTORIAL` or an integer-date function when that range does
  not hold their inner-dmax 0, a quotient whose operand was cut, an argument of `ORD-MAX` or
  `ORD-MIN` that can need more than 30 digits), a `DIVIDE` with an intermediate quotient (several
  `GIVING` receivers, `ROUNDED`, `REMAINDER`) and a `MULTIPLY ... ROUNDED` without `GIVING` that
  can need more than 30 digits: unsupported;
- the extra decimal place with `ROUNDED`, an assumption: IBM says that with `ROUNDED` "one more
  decimal place might be carried for accuracy if necessary" (Enterprise COBOL 6.4 Programming
  Guide, "Terminology used for intermediate results"), not when. The model reads it as: the place
  is carried whenever IBM's base scale max(d2 - d1, dmax) does not already exceed the receiver's
  places, that is, whenever the receiver's rounding needs it, which for `ROUNDED` (nearest, away
  from zero) gives the stored value of rounding the exact quotient. The model carries the extra
  place for every quotient of a `COMPUTE` with a `ROUNDED` receiver, which stores the same values.
  Open: a quotient inside a larger expression of a `ROUNDED` `COMPUTE`, where the extra place
  reaches the later operations (no such statement is in NIST, CardDemo or the theorem programs);
- `ROUNDED MODE`, which Enterprise COBOL 6.4 and 6.5 do not have (only `ROUNDED`: Language
  Reference, "ROUNDED phrase"): the model also implements COBOL 2014's rounding modes; with plain
  `ROUNDED` and with truncation every statement follows IBM's rules. A quotient that is the whole
  result of a `DIVIDE` or `COMPUTE` is rounded from its exact value under every mode (`COMPUTE Q
  ROUNDED MODE NEAREST-EVEN = A / B` with A 251, B 100, Q `PIC 9` is 3, as the `DIVIDE`); a
  quotient inside a larger expression is IBM's intermediate result, which the receiver's mode then
  rounds;
- `SEARCH ALL` with an alphanumeric `KEY` in a program whose collating sequence is an `ALPHABET`
  of literals (the model checks the table's `KEY` order in native order);
- class conditions with a class name in a program whose collating sequence is an `ALPHABET` of
  literals (the front end's comparisons would be collated), on an item that is not `USAGE
  DISPLAY`, on a group containing an `OCCURS DEPENDING ON` table, on a reference modification
  whose length is not a literal, on a function, and of more than 4096 comparisons;
- `DISPLAY` of a numeric literal with decimal places under `DECIMAL-POINT IS COMMA`: not checked
  (IBM's rules for numeric literals give its digits only, the decimal point being an assumed one
  that takes no character position; the model shows such a literal that way without the clause,
  and GnuCOBOL 3.2 does with and without it);
- `DISPLAY` of a signed numeric literal: IBM gives no form for the sign (GnuCOBOL 3.2 writes `-15`
  and `+15`);
- the `EXIT SECTION` interpretation follows IBM (GnuCOBOL differs);
- reads of out-of-`PICTURE` binary values under TRUNC(BIN) are not validated (GnuCOBOL is
  inconsistent there: it DISPLAYs the full binary value but uses it truncated to the `PICTURE` in
  arithmetic, in one `ADD` even for one receiver and not for the other; the model uses the full
  value). `tools/difftest/bin_cases/` keeps the three programs where a random TRUNC(BIN) run
  (200 programs, seed 12) differs for that reason (case 130 shows only in the per-statement
  outcome trace; `t130x.cob` is a minimal reproduction), and `tools/evidence/bin_trace.sh`
  shows it.

**Proof-side limits:**
- Loops whose iteration count depends on the data (read a file until its end) need a loop
  invariant, stated by hand; `cobol_loop` turns it into four obligations that the automation
  proves (RECSUM).
  - Only `PERFORM … UNTIL` with the test before is covered. An iteration may leave the loop
    (an abend, `NEXT SENTENCE`): `cobol_loop_exit` (`Cobol/Logic/LoopExit.lean`).
  - Loops with constant bounds unroll within the fuel.
- Long straight-line code costs roughly quadratic time in the number of statements.
- `PERFORM` summaries are stated by hand, and so far only for one-paragraph ranges that
  return normally.
- Identities between different rounding pipelines must be stated as lemmas (as `have`).
- The bounds simprocs are path-insensitive: a store that only fits because of an enclosing
  test keeps its `fitNum`, and `cobol_grind` handles it by case analysis.
