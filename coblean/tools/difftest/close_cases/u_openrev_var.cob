      * OPEN INPUT ... REVERSED of a variable-length file. IBM: "When OPEN
      * REVERSED is specified, the record format must be fixed"
      * (Language Reference 6.4, OPEN statement): the model stops with
      * unsupported at V02. (GnuCOBOL 3.2 ignores REVERSED.)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UOPNREVV.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F4 ASSIGN TO "uopnrevv-f4.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST4.
       DATA DIVISION.
       FILE SECTION.
       FD F4 RECORD VARYING IN SIZE FROM 1 TO 8 CHARACTERS
           DEPENDING ON L4.
       01 R4 PIC X(8).
       WORKING-STORAGE SECTION.
       01 ST4 PIC XX VALUE "..".
       01 L4 PIC 9 VALUE 8.
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F4
           CLOSE F4
           DISPLAY "V01 " ST4 "|"
           OPEN INPUT F4 REVERSED
           DISPLAY "V02 REV " ST4 "|"
           STOP RUN.
