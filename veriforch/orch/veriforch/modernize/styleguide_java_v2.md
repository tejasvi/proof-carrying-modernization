# Target style guide: COBOL batch program → Java

Translate the program into ONE Java class whose entry point holds the program's business logic. Behaviour must
match the COBOL program exactly, on every input, byte for byte. That covers every DISPLAY line, every record
written or rewritten, the return code, and when the program abends. Reproduce what the COBOL code does, including
its quirks and defects. Do not fix, improve or reinterpret it.

## Shape

* Class `<Program>` (PROGRAM-ID in PascalCase, e.g. `Cbact02c`), `public final`. No package.
* Entry point: `public static Result run(<inputs...>)`. Its parameters, in this order:
  - one parameter per file the program OPENs INPUT or I-O (even if it never reads it), in SELECT order: an array
    of records in file order; an indexed file comes in key order. Type: the record class of the 01 item the program
    reads the file INTO, or of the file's FD record if it reads the file without INTO or never reads it. Name: the FD name by the naming rule (e.g. `CARDFILE-FILE` → `cardfileFile`);
  - if the program has `PROCEDURE DIVISION USING`: one parameter per USING item, in order, named by the item in
    camelCase. A group item is a record class (naming rule below); an elementary item has its field type;
  - `String clock` LAST, only if the program uses FUNCTION CURRENT-DATE: the 21-character value it returns.
* `Result` is a `public static final class Result` nested in the class, with public non-static fields:
  - `java.util.List<String> displays`: every DISPLAY line in order, as text;
  - for each output file the program WRITEs: `java.util.List<R> <file>Writes`, with R the record class written
    FROM (e.g. `TRANSACT-FILE` → `transactFileWrites`);
  - for each file the program REWRITEs: `java.util.List<R> <file>Rewrites`;
  - for a file whose FD says `RECORD IS VARYING ... DEPENDING ON`, the writes are text instead: `java.util.List<String>
    <file>Writes`, each element the record as written, exactly as many characters as the record's length at the
    WRITE (alphanumeric data as is, zoned numerics in their display form, sign overpunched in the last digit);
  - `int returnCode` only if the program sets RETURN-CODE;
  - `boolean abended`: true if the program abends (CALL 'CEE3ABD'). Processing stops there, and everything
    displayed or written before is kept.
* A routine the program CALLs whose source is given (e.g. an assembler module) is translated as private helper
  code in the same class.
* No I/O in the entry point: no files, no System.out, no exceptions escaping. A `main` method is optional and not
  used.
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

* A record class per 01 item used as a file record or a FROM/INTO area: the 01 name in PascalCase
  (`CARD-RECORD` → `CardRecord`), `public static final class` nested in the program class.
* Groups below 01 are FLATTENED: the class has one field per elementary item, in copybook order, named by the
  elementary item in camelCase (`ACCT-CURR-BAL` → `acctCurrBal`). FILLER items are `filler1`, `filler2`, …,
  numbered per record in copybook order. A REDEFINES item contributes no fields (use the redefined item's fields).
* Each record class has public non-static fields and one constructor taking all fields in that order.

## Types

* Numeric items (any usage, `PIC S9(n)V9(s)`, n + s ≤ 18): `long` holding the scaled integer value × 10^s (cents
  for V99). Never `double`, `float` or `BigDecimal`.
* Alphanumeric `PIC X(n)` / `A(n)`: `String` of exactly n characters (the text, trailing spaces included).
* `OCCURS k` on an elementary item, or on a group (then on every elementary item under it): an array `T[]` of
  length k per elementary item, so a group's items become parallel arrays (`ARR-ACCT-BAL OCCURS 5` holding
  `ARR-ACCT-CURR-BAL` gives `long[] arrAcctCurrBal` of length 5).

## Code restrictions (the result is verified, and these keep it in the verifier's language)

* Plain loops, `if`/`else`, `switch` on ints, arrays, `java.util.ArrayList` / `List`, `String` / `StringBuilder`,
  `long` / `int` / `boolean` / `char`.
* No streams, lambdas, method references, generics beyond `List<R>`, reflection, threads, exceptions for control
  flow, `java.time`, `String.format`, regular expressions.
* Helpers (zero padding, number formatting, sign handling, …) are private static methods of the same class,
  written with plain loops.

## Structure for verification

The translation is proved equivalent to the COBOL program method by method, so its structure matters:

* Every search over a file's records (a keyed READ, any lookup by key) is a private static helper method that
  contains the loop and returns the index of the record found, or -1. `run` calls the helper; no search loop is
  written inline in `run`.
* No large constant tables: no `static` arrays with initializers (e.g. a 256-entry code-page table). Encode such a
  table as a `String` constant indexed with `charAt`, or compute it with arithmetic in a small helper method.
* Keep the state that lives across `run`'s main loop small: declare locals in the narrowest scope, and put the
  per-record work into helper methods.
* Build output text with `StringBuilder.append`; do not write characters into a `char[]` by index.
