      * OPEN OUTPUT ... REVERSED. IBM: REVERSED is a phrase of OPEN INPUT
      * only (Language Reference 6.4, OPEN statement, format 1): the
      * front end reports the OPEN as unsupported. (GnuCOBOL 3.2 ignores
      * REVERSED.)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UOPNREVO.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "uopnrevo-f1.dat"
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
           DISPLAY "O01 " ST1 "|"
           OPEN OUTPUT F1 REVERSED
           DISPLAY "O02 REV " ST1 "|"
           STOP RUN.
