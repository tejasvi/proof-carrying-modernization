      * INITIALIZE ... REPLACING of a condition name: a named unsupported
      * statement (initptr_checks.sh).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. PTR3.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A PIC X.
           88 A-YES VALUE 'Y'.
       PROCEDURE DIVISION.
       MAIN-PARA.
           INITIALIZE A-YES REPLACING ALPHANUMERIC BY 'N'
           STOP RUN.
