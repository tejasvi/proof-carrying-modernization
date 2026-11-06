# Item A: certified modernization of CardDemo batch programs: shared interfaces

Programs: CBACT02C, CBACT03C, CBACT04C, CBCUS01C, CBTRN01C, from aws-samples/aws-mainframe-modernization-carddemo
@ 59cc6c2, in `targets/carddemo_src/carddemo/app/{cbl,cpy}`. coblean's IR is
`coblean/examples/carddemo/<prog>.ir.json`; the front end on these sources reproduces it.

There are two translation arms per program and target language (Java, Rust):
* the **guided** arm: the LLM sees the COBOL source, the copybooks and the fixed style guide
  (`styleguide_java.md` / `styleguide_rust.md`);
* the **naive** arm: the LLM sees the COBOL source, the copybooks and only "translate this COBOL program to idiomatic
  Java/Rust", plus the fixed I/O contract below, which is needed to run it.

Every attempt is recorded under `runs/modernize/<PROG>/<arm>/<lang>/v<k>/`.

## Test case (input) JSON: one per generated input, written by the input generator

```json
{
  "program": "CBACT02C",
  "clock": "2025102314301234-0500",
  "files": {
    "CARDFILE-FILE": {"record": "CARD-RECORD", "records": [ {"CARD-NUM": "4000000000000001", "CARD-ACCT-ID": 12, ...}, ... ]}
  }
}
```
* `files` holds each INPUT file by its FD name, with the record the program reads it INTO (01 name). Records are in
  file order; indexed files come in key order.
* Values come per elementary field, by COBOL name, with groups flattened:
  - a numeric field is a JSON integer, the scaled value (value × 10^scale; signed only if the PIC is signed);
  - an alphanumeric field is a JSON string of exactly the field length (the CP037-decoded characters; every char is
    in U+0000..U+00FF);
  - each FILLER is `"FILLER#k"` (k = 1, 2, … per record in copybook order);
  - an OCCURS field is a JSON list.
* `clock` is the value FUNCTION CURRENT-DATE returns (21 chars) when the program reads the clock.
* `linkage` (only for programs with `PROCEDURE DIVISION USING`) holds each USING item by its 01 name: a group as an
  object of field values (same convention as records), an elementary item as its value. Example (CBACT04C):
  `"linkage": {"EXTERNAL-PARMS": {"PARM-LENGTH": 10, "PARM-DATE": "2026-10-24"}}`.
* For cobolrun, a record is encoded by the layout of the record the program reads it INTO, then padded with spaces
  or truncated to the FD record's length (CBTRN03C reads 80-byte DATEPARM records INTO a 21-byte area).

## Initial storage (the convention every translation and every theorem uses)

COBOL leaves storage without a VALUE clause undefined, and some outputs depend on it (measured: CBACT04C's
TRANSACT records, the FILLERs CBTRN02C writes, CBTRN01C's display of a never-read record). One fixed convention,
INITIALIZE-like:
* every byte starts as X'40' (EBCDIC space);
* each elementary numeric item outside REDEFINES subtrees (every occurrence; every 01 that is not itself a
  REDEFINES) holds coblean's encoding of 0 (zoned F0…F0, signed: last byte C0; packed 0…0C or 0…0F; binary zero);
* alphanumeric, numeric-edited and FILLER items stay spaces.

`runs/modernize/<PROG>/init_mem.hex` is that storage byte for byte: the `m` of `Program.initState m inp`, which
coblean's `initMem` overwrites with the VALUE clauses. The harness writes the case's linkage values over the
linkage items and passes the result to `cobolrun --mem`. Each case also runs on two random storages with valid
numeric items; if the outcome changes, the case is marked `init_dependent` (its outcome depends on the
convention).

## Outcome (output) JSON: the same canonical form for COBOL (cobolrun) and every translation

```json
{
  "end": "normal" | "abend",
  "displays": ["START OF EXECUTION OF PROGRAM CBACT02C", "..."],
  "writes":   {"<FD name>": [ {<COBOL field>: value, ...}, ... ]},
  "rewrites": {"<FD name>": [ ... ]},
  "return_code": 0
}
```
* `displays` are the DISPLAY lines as Unicode strings (CP037-decoded for COBOL; Latin-1 decoded `Vec<u8>` for Rust).
* `writes` / `rewrites` hold the records per output FD, decoded by the record layout the program WRITEs FROM, in the
  same field convention as the input.
* `end` is `abend` when the program calls CEE3ABD (or coblean reports a non-normal end). Displays up to the abend
  are kept.
* `return_code` is null when the program never sets RETURN-CODE.

## Runner contract (implemented per language)

`run(<translation dir>, <test case JSON>) -> <outcome JSON>` or a failure kind:
* `compile_error`: javac fails, or Soot/JimpleLean import fails (guided arm), or cargo fails, or Charon/Aeneas
  rejects the crate (guided arm). The message goes back to the model as a compile error.
* `runtime_error`: an exception, panic or timeout.
* the outcome.

Each runner reports which executions produced the outcome:
* Java: native JVM, and jimple-run (JimpleLean's interpreter on the Jimple from Soot).
* Rust: native, and the Aeneas extraction evaluated in Lean.

When the two disagree, that is a finding in its own right (front-end or model bug).

## Naive-arm I/O contract (all the naive prompt adds to "translate this program")

* Java: a program whose main class is the PROGRAM-ID in PascalCase (`Cbact02c`), default package; Rust: a binary
  crate named by the PROGRAM-ID in lowercase (`cbact02c`), no dependencies.
* The program reads each input file from the current directory under its ASSIGN name (e.g. `CARDFILE`). Files are
  line-sequential UTF-8 text, one record per line: the record image in copybook layout with every EBCDIC byte
  shown as its code page 037 character. So zoned digits are digit characters, and a signed zoned field ends in an
  overpunch character ('{' and 'A'-'I' positive, '}' and 'J'-'R' negative). There are no packed or binary fields:
  CardDemo's batch records are all DISPLAY usage. Output files are written the same way under their ASSIGN names.
* DISPLAY output goes to stdout, one line each.
* FUNCTION CURRENT-DATE returns the value of the environment variable `COBOL_CURRENT_DATE` (21 characters).
* A program with `PROCEDURE DIVISION USING` receives its JCL EXEC PARM text as the first command-line argument.
  The runner passes the text fields of the case's linkage record, and sets the case's length field to the text's
  length.
* The exit status is the program's RETURN-CODE (0 when it never sets it). On abend, the program prints its
  messages and exits with status 999.
