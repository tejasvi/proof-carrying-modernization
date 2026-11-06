      * OPEN INPUT ... REVERSED of a disk file of two records. IBM:
      * REVERSED "does not apply" to a direct-access device (Language
      * Reference 6.4, OPEN statement) and does not say where the READs
      * then start: the model stops with unsupported at R02. (GnuCOBOL
      * 3.2 ignores REVERSED and reads the records forward.)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UOPNREVM.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "uopnrevm-f1.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F1
           MOVE "FIRSTXXX" TO R1
           WRITE R1
           MOVE "SECONDXX" TO R1
           WRITE R1
           CLOSE F1
           DISPLAY "R01 " ST1 "|"
           OPEN INPUT F1 REVERSED
           DISPLAY "R02 REV " ST1 "|"
           READ F1
           DISPLAY "R03 " ST1 " " R1 "|"
           STOP RUN.
