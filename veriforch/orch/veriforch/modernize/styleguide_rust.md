# Target style guide: COBOL batch program → Rust

Translate the program into ONE Rust library crate whose entry point holds the program's business logic. Behaviour
must match the COBOL program exactly, on every input, byte for byte. That covers every DISPLAY line, every record
written or rewritten, the return code, and when the program abends. Reproduce what the COBOL code does, including
its quirks and defects. Do not fix, improve or reinterpret it.

## Shape

* Crate `<program>` (PROGRAM-ID in lowercase, e.g. `cbact02c`): one file `src/lib.rs` (edition 2021) and its
  `Cargo.toml` (no dependencies).
* Entry point: `pub fn run(<inputs...>) -> Output`. Its parameters, in this order:
  - one parameter per file the program OPENs INPUT or I-O (even if it never reads it), in SELECT order: a slice of
    records in file order; an indexed file comes in key order. Type: `&[R]`, with R the record struct of the 01 item
    the program reads the file INTO, or of the file's FD record if it reads the file without INTO or never reads it. Name: the FD name by the naming rule (e.g. `CARDFILE-FILE` → `cardfile_file`);
  - if the program has `PROCEDURE DIVISION USING`: one parameter per USING item, in order, named by the item in
    snake_case. A group item is a record struct passed by reference (`&R`, naming rule below); an elementary
    item has its field type;
  - `clock: &[u8; 21]` LAST, only if the program uses FUNCTION CURRENT-DATE: the value it returns.
* `Output` is a `pub struct` with pub fields:
  - `displays: Vec<Vec<u8>>`: every DISPLAY line in order, one byte per character;
  - for each output file the program WRITEs: `<file>_writes: Vec<R>`, with R the record struct written FROM (e.g.
    `TRANSACT-FILE` → `transact_file_writes`);
  - for each file the program REWRITEs: `<file>_rewrites: Vec<R>`;
  - for a file whose FD says `RECORD IS VARYING ... DEPENDING ON`, the writes are bytes instead:
    `<file>_writes: Vec<Vec<u8>>`, each element the record as written, exactly as many bytes as the record's
    length at the WRITE (alphanumeric data as is, zoned numerics in their display form, sign overpunched in the
    last digit);
  - `return_code: i64` only if the program sets RETURN-CODE;
  - `abended: bool`: true if the program abends (CALL 'CEE3ABD'). Processing stops there, and everything displayed
    or written before is kept.
* A routine the program CALLs whose source is given (e.g. an assembler module) is translated as private helper
  functions in the same crate.
* No I/O in the entry point: no files, no `println!`, no panics on valid input. A `main` is not part of the crate.
* Storage: an item without a VALUE clause starts as if INITIALIZEd: numeric items are zero; alphanumeric and
  numeric-edited items and FILLERs are spaces. This holds for WORKING-STORAGE and for the FD record areas before
  the first READ.
* Files: there is no real I/O; each input parameter holds the file's initial contents. The file statuses follow
  IBM Enterprise COBOL (QSAM sequential, VSAM KSDS indexed):
  - OPEN and CLOSE succeed (status '00'); OPEN OUTPUT starts the file empty.
  - Sequential READ: the next record ('00'), or end of file ('10') after the last one; a READ after that gives '46'.
  - Keyed READ (record key or alternate key): the record whose key equals the current value of the key field in
    the file's record area ('00'), or INVALID KEY ('23') when there is none.
  - WRITE to a sequential file appends the record ('00'). WRITE to an indexed file fails with INVALID KEY ('22')
    when a record with the same record key (or the same unique alternate key) exists, including records written
    earlier in the run; otherwise it adds the record ('00') and later READs find it.
  - REWRITE to an indexed file (random access) replaces the record with the same record key ('00'), or fails with
    INVALID KEY ('23'); later READs see the new contents.
  - Only successful WRITEs and REWRITEs appear in the output lists. Translate the program's own handling of the
    statuses.

## Naming rule (mechanical; the proof's field relations depend on it)

* A record struct per 01 item used as a file record or a FROM/INTO area: the 01 name in PascalCase
  (`CARD-RECORD` → `CardRecord`).
* Groups below 01 are FLATTENED: one field per elementary item, in copybook order, named by the elementary item in
  snake_case (`ACCT-CURR-BAL` → `acct_curr_bal`). FILLER items are `filler1`, `filler2`, …, numbered per record in
  copybook order. A REDEFINES item contributes no fields (use the redefined item's fields).
* `pub struct` with pub fields, `#[derive(Clone, Copy)]` (every field type below is Copy).

## Types

* Numeric items (any usage, `PIC S9(n)V9(s)`, n + s ≤ 18): `i64` holding the scaled integer value × 10^s (cents
  for V99).
* Alphanumeric `PIC X(n)` / `A(n)`: `[u8; n]`, one byte per character (the characters' code points, all
  ≤ 0xFF). Never `String` or `&str`.
* `OCCURS k` on an elementary item, or on a group (then on every elementary item under it): `[T; k]` per
  elementary item, so a group's items become parallel arrays (`ARR-ACCT-BAL OCCURS 5` holding
  `ARR-ACCT-CURR-BAL` gives `arr_acct_curr_bal: [i64; 5]`).

## Code restrictions (the result is verified, and these keep it in the verifier's language)

* `while` / `for i in 0..n` loops over indices, `if` / `else`, `match` on integers, arrays, slices, `Vec` with
  `push` / indexing / `len`, `i64` / `u64` / `u128` / `usize` / `u8` / `bool`.
* No iterator adapters (`map`, `filter`, `collect`, …), closures, traits beyond `#[derive(Clone, Copy)]`, `dyn`,
  `String` / `&str` / `format!` / `println!`, floating point, `unsafe`.
* No assignment to a field of an indexed element (`v[i].f = x`): copy the element into a local, update the local,
  store it back (`let mut e = v[i]; e.f = x; v[i] = e;`).
* Helpers (zero padding, number formatting, sign handling, …) are private functions in the same file, written
  with plain loops.
