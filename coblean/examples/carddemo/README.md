# AWS CardDemo batch programs: IRs, runs, abstractions

Source: [AWS CardDemo](https://github.com/aws-samples/aws-mainframe-modernization-carddemo)
(Apache-2.0), unmodified, in `~/coblean_corpus/carddemo/src` (programs `app/cbl`, copybooks
`app/cpy`, sample data `app/data/EBCDIC`). Each `*.ir.json` here is the front end's output on
the unmodified source:

```sh
python3 -I tools/cobolfe/cobolfe.py app/cbl/PROG.cbl -I app/cpy --tab-width 4 -o prog.ir.json
```

`--tab-width 4` matters only for the two copybooks that contain tab characters (`CUSTREC.cpy`,
`CSLKPCDY.cpy`): with 4-column tab stops every line ends before column 73, with 8-column stops
17 lines of `CUSTREC.cpy` run past column 72 and their PICTURE strings are cut. Real
fixed-format source has no tabs, so this is an assumption about the author's editor.

CBSTM03A calls CBSTM03B (`CALL 'CBSTM03B'`, a static call on IBM). `tools/cobolfe/link.py` puts
the callee's IR into the caller's:

```sh
python3 -I tools/cobolfe/cobolfe.py app/cbl/CBSTM03A.CBL -I app/cpy --tab-width 4 -o a.json
python3 -I tools/cobolfe/cobolfe.py app/cbl/CBSTM03B.CBL -I app/cpy --tab-width 4 -o b.json
python3 -I tools/cobolfe/link.py a.json b.json -o cbstm03ab.ir.json
```

## Programs

| Program | IR | Status | All-input theorem |
|---|---|---|---|
| CBACT01C | `cbact01c.ir.json` | 0 unsupported; runs on the sample accounts with `--externals carddemo` | `cbact01c_extracts` |
| CBACT02C | `cbact02c.ir.json` | 0 unsupported | `cbact02c_lists` |
| CBACT03C | `cbact03c.ir.json` | 0 unsupported | `cbact03c_lists` |
| CBACT04C | `cbact04c.ir.json` | 0 unsupported | `cbact04c_every` (every input), `cbact04c_all`, `cbact04c_events` (every event) |
| CBCUS01C | `cbcus01c.ir.json` | 0 unsupported | `cbcus01c_lists` |
| CBTRN01C | `cbtrn01c.ir.json` | 0 unsupported | `cbtrn01c_verifies`, `cbtrn01c_verifies_all` |
| CBTRN02C | `cbtrn02c.ir.json` | 0 unsupported; runs on the sample data; functional model checked against it | `cbtrn02c_posts`, `cbtrn02c_any` (any ids: abend at the first duplicate) |
| CBTRN03C | `cbtrn03c.ir.json` | 0 unsupported; runs on CBTRN02C's output; functional model checked against it | `cbtrn03c_every` (every input), `cbtrn03c_any`, `cbtrn03c_report`, `cbtrn03c_stops` |
| CBSTM03A + CBSTM03B | `cbstm03ab.ir.json` (linked) | 0 unsupported; runs on CBTRN02C's output and the sample data; every output record equals GnuCOBOL's | – |
| CBEXPORT, CBIMPORT | – | rejected: `RECORD KEY` outside the file's record area (invalid on IBM) | – |

## Theorems and what they assume

Every theorem holds for any initial storage (bytes the program reads without setting them are
model parameters), for input files whose records are well formed (each decodes into the model's
record structure: field lengths and numeric ranges), and for any sufficient fuel
(`Program.run_mono`). The other assumptions:

| Program | Theorems | Other assumptions |
|---|---|---|
| CBACT01C | `cbact01c_extracts` | COBDATFT supplied by the environment (modelled from its source) |
| CBACT02C, CBACT03C, CBCUS01C | `cbact02c_lists`, `cbact03c_lists`, `cbcus01c_lists` | none |
| CBACT04C | `cbact04c_every` (`cbact04c_all`, `cbact04c_events`: lookups succeed, the disclosure group found directly) | distinct account ids among the category records (a KSDS read in key order gives ascending ids); fewer than 999 999 category records; clock readings in the `CURRENT-DATE` form. The sample data takes the `DEFAULT` group path for every record (every account's group id is blank), which only `cbact04c_every` covers |
| CBTRN01C | `cbtrn01c_verifies`, `cbtrn01c_verifies_all` | none |
| CBTRN02C | `cbtrn02c_any` (`cbtrn02c_posts`: distinct ids) | clock readings in the `CURRENT-DATE` form; fewer than 10^9 transactions |
| CBTRN03C | `cbtrn03c_every` (`cbtrn03c_any`: no blank card number; `cbtrn03c_report`: dates in range, lookups succeed; `cbtrn03c_stops`: a date out of range) | fewer than 10^7 transactions; for an empty file, the record area's initial contents decode as a transaction record (the end-of-file iteration re-tests its date); when the first card number is blank, the initial `XREF-ACCT-ID` holds an account id (leading blank cards are reported with it, without a lookup) |

## Abstractions and environment

- **Clock.** `FUNCTION CURRENT-DATE` reads `Env.clock k` (the `k`-th reading; `cobolrun --clock`
  returns one reading every time).
- **Abend.** `CALL 'CEE3ABD'` ends the run with `Signal.fault (.abend code)`. Every program
  abends this way on an unexpected file status (for example a duplicate key on `WRITE`).
- **COBDATFT** (`app/asm/COBDATFT.asm`, HLASM, called by CBACT01C) is modelled by
  `Cobol/Ext/CardDemo.lean`, transcribed from the source: the two date reformattings. Its error
  path is left `unsupported`: it moves 38 bytes from a 13-byte literal, so 25 bytes come from the
  routine's literal pool, which the source does not determine. CBACT01C only takes the valid
  path. `cobolrun --externals carddemo` supplies it; without it `CALL 'COBDATFT'` is
  `unsupported`.
- **RETURN-CODE** is an ordinary storage item (the front end declares it, `VALUE 0`). The
  semantics does not set it after a `CALL`. COBDATFT returns 0, so that agrees.
- **Files.** VSAM KSDS = a list of records in key order (`Cobol/Sem/File.lean`, IBM file status
  codes); sequential datasets = lists of fixed-length records. The sample datasets are cut into
  records with `tools/coverage/carddemo_inputs.py`.
- **Uninitialized storage** without `VALUE` is whatever the initial storage holds (`cobolrun`:
  zeros, `--mem` to choose). Some of it reaches output records (below).
- **Static `CALL`** (CBSTM03A to CBSTM03B). In the linked IR, `CALL 'CBSTM03B' USING area` is
  `callLocal`: it copies `area` into CBSTM03B's `LINKAGE` item, runs CBSTM03B from its first
  paragraph, and copies the item back when CBSTM03B returns (`GOBACK`). CBSTM03B keeps its
  storage and its open files from one call to the next, as an IBM static call without `CANCEL`
  does. Copying in and out equals `BY REFERENCE` here: CBSTM03B reaches the area under no other
  name. A `GOBACK` paragraph separates the two procedure divisions; CBSTM03A ends with its own
  `GOBACK` and never reaches it.
- **z/OS control blocks.** CBSTM03A first follows the chain PSA, TCB, TIOT from address 0 and
  displays the job name, the step name and the DD names. `SET ADDRESS OF item TO p` copies the
  item's length in bytes from `Env.addrSpace` at address `p` into the item. CBSTM03A only reads
  these items (a write to one would not reach the address space). `cobolrun --addrspace` reads
  the address space; `tools/coverage/creastmt_inputs.py` builds one for CREASTMT.jcl's step
  (job CREASTMT, step STEP040, 9 DD statements). `PSAPTR` has no `VALUE`: the walk starts at
  address 0 only if initial storage holds zeros there (as in `cobolrun` without `--mem`).
- **`ALTER`** (CBSTM03A chooses the next file to open with it): the front end gives each altered
  paragraph a hidden switch item; `ALTER p TO PROCEED TO q` sets the switch, and the paragraph's
  `GO TO` becomes a `GO TO … DEPENDING ON` the switch.
- **JCL steps outside the programs** are not modelled. `tools/coverage/tranrept_inputs.py`
  builds CBTRN03C's input as TRANREPT.jcl's SORT does. `tools/coverage/creastmt_inputs.py`
  builds CBSTM03A's TRNXFILE as CREASTMT.jcl's SORT and REPRO do: CBTRN02C's transaction
  records sorted by card number and transaction id and rearranged by the `OUTREC` (328 bytes),
  padded with blanks to the 350-byte record (an assumption about DFSORT's padding).

## Runs on the sample data

```sh
D=~/coblean_corpus/carddemo/src/app/data/EBCDIC
python3 -I tools/coverage/carddemo_inputs.py t2.json 1:350:$D/AWS.M2.CARDDEMO.DALYTRAN.PS \
  3:50:$D/AWS.M2.CARDDEMO.CARDXREF.PS 5:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS \
  6:50:$D/AWS.M2.CARDDEMO.TCATBALF.PS
.lake/build/bin/cobolrun examples/carddemo/cbtrn02c.ir.json --inputs t2.json \
  --clock 2025102414300000-0500 > t2.out.json
python3 -I tools/coverage/tranrept_inputs.py t2.out.json 2025-10-01 2025-10-31 $D t3.json
.lake/build/bin/cobolrun examples/carddemo/cbtrn03c.ir.json --inputs t3.json > t3.out.json
python3 -I tools/coverage/carddemo_inputs.py t1.json 1:300:$D/AWS.M2.CARDDEMO.ACCTDATA.PS
.lake/build/bin/cobolrun examples/carddemo/cbact01c.ir.json --inputs t1.json --externals carddemo
python3 -I tools/coverage/creastmt_inputs.py t2.out.json $D t4.json t4as.json
.lake/build/bin/cobolrun examples/carddemo/cbstm03ab.ir.json --inputs t4.json --addrspace t4as.json \
  > t4.out.json
```

- **CBTRN02C** (300 daily transactions, 50 accounts, 50 cross-references, 50 category balances):
  `GOBACK`, 262 posted (262 transaction records written, 262 account `REWRITE`s, 50 new and 212
  rewritten category balances), 38 rejected (all reason 102, over limit), RETURN-CODE 4. The
  functional model in `Examples/Cbtrn02c.lean` (`model`: validate, then post or reject, one
  transaction at a time) gives the same 878 events and the same RETURN-CODE on this data. Every
  sample record decodes into the model's record structures and re-encodes to the same bytes.
- **CBTRN03C** (CBTRN02C's 262 transaction records, sorted by card number): `GOBACK`, a
  451-line report (718 events with the DISPLAYs). The functional model in `Examples/Cbtrn03c.lean`
  (`report3`, a fold over the transactions, then `eofEvents`) gives the same 718 events, from
  zeroed and from patterned initial storage, and on each of the first 60 prefixes of the file.
- **CBACT01C** (50 accounts): `GOBACK`, 50 output records (with COMP-3 fields), 50 array
  records, 100 variable-length records (12 and 39 bytes), 50 `CALL 'COBDATFT'`.
- **CBSTM03A + CBSTM03B** (CBTRN02C's 262 transaction records for 50 cards, at most 6 per card;
  50 cross-references, customers and accounts): `GOBACK`, 11 `DISPLAY` lines (job, step and the
  9 DD names), 50 statements as 1212 text lines (STMT-FILE, 80 bytes) and 6082 HTML lines
  (HTML-FILE, 100 bytes). Checked against GnuCOBOL 3.2: the same run in ASCII (IR extracted with
  `cobolfe.py --profile gnucobol`, inputs converted from code page 037 field by field) writes
  exactly the records that GnuCOBOL writes when it compiles the unmodified CBSTM03B and CBSTM03A
  without its control-block walk (lines 266-291, which read z/OS storage). All 7294 records are
  equal byte for byte (`tools/difftest/stm_ascii.py`, `stm_gnucobol.sh`, `stm_compare.py`).

## Behaviors a rewrite must reproduce or knowingly change

- CBTRN02C: the transaction record's last 20 bytes (`FILLER` of WORKING-STORAGE's
  `TRAN-RECORD`) and a new category balance record's last 22 bytes (`FILLER` of
  `TRAN-CAT-BAL-RECORD`: from initial storage, or the last record read) come from storage the
  program never sets. A transaction that fails both checks gets reason 103 (the expiration
  check runs second and overwrites 102). Balances that overflow their PICTURE are truncated
  (no `ON SIZE ERROR`). A duplicate transaction id abends on the transaction file `WRITE`,
  after that transaction's category balance and account have already been rewritten.
- CBTRN03C: at end of file the last transaction's amount is added to the totals again, so the
  last page total and the grand total count it twice; the last account's total line is never
  written. `NEXT SENTENCE` inside the main `PERFORM UNTIL` leaves the loop: a transaction outside
  the date range ends the report there (TRANREPT.jcl's SORT step filters on the same range, so
  this does not happen in the delivered job).
- CBACT01C: `OUT-ACCT-REISSUE-DATE` takes 10 bytes of COBDATFT's 20-byte output date, of which
  COBDATFT sets 8; the last 2 bytes are initial storage.
- CBTRN01C: the last transaction's lookup messages are displayed twice (`cbtrn01c_verifies`).
- CBACT04C: the last account's interest is never posted
  ([issue #64](https://github.com/aws-samples/aws-mainframe-modernization-carddemo/issues/64));
  `cbact04c_all` states it for every input.
- CBACT03C, CBCUS01C: every record is displayed twice.
- CBSTM03A: all transactions are first loaded into a table of 51 cards with 10 transactions
  each (`OCCURS 51`, `OCCURS 10`). A 52nd card or an 11th transaction for one card falls outside
  the table: undefined on IBM without `SSRANGE`, a range fault (`Fault.range`) in the semantics.
  An empty transaction file abends: the first `READ` right after `OPEN` accepts only status 00
  or 04, so end of file (10) displays `ERROR READING TRNXFILE` and calls `CEE3ABD`, and no
  statement is written even when there are accounts. `CEE3ABD` is called without arguments, so
  the abend code is not determined by the program (the semantics reports `abend (-1)`).
  The TCB address is read at PSA offset 536 (X'218', `PSATNEW` in IBM's PSA mapping; the current
  TCB is `PSATOLD`, X'21C'). The DD name line after the walk loop ends `-- null  UCB` where the
  loop's line ends `--  null UCB`.

## Coverage over all CardDemo programs

`tools/coverage/carddemo_coverage.py` runs the front end and the resolver on every program
(44, in `app/cbl` and the three optional modules; 22 904 non-comment lines without copybooks):

| Kind | Programs | Through front end + semantics, 0 unsupported | Other |
|---|---|---|---|
| batch | 14 (4 684 lines) | 12 (3 951 lines): CBACT01C–04C, CBCUS01C, CBSTM03A (linked with CBSTM03B), CBSTM03B, CBTRN01C–03C, COBSWAIT (`ACCEPT FROM SYSIN`: the system input device's records come from `cobolrun --sysin`; run without them it stops at the `ACCEPT`, with them at `CALL 'MVSWAIT'`, an assembler routine the environment does not provide), CSUTLDTC (`OCCURS DEPENDING ON`; run alone it stops at `CALL 'CEEDAYS'`, a Language Environment service the environment does not provide) | CBEXPORT, CBIMPORT rejected (invalid `RECORD KEY`) |
| IMS batch | 4 | – | DBUNLDGS, PAUDBLOD, PAUDBUNL extract with 1 unsupported each (`ENTRY`); CBPAUP0C (`EXEC DLI` fields) |
| DB2 batch | 1 | – | COBTUPDT (`EXEC SQL`) |
| CICS online (with DB2/IMS/MQ) | 25 | – | no CICS model: the front end stops at the CICS/MQ system copybooks (`DFHAID`, `DFHBMSCA`, `CMQ*`) |
