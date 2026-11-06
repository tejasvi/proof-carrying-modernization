      * OPEN INPUT ... REVERSED of an indexed file. IBM: "REVERSED is
      * not valid for VSAM files" (Language Reference 6.4, OPEN
      * statement): the front end reports the OPEN as unsupported.
      * (GnuCOBOL 3.2 ignores REVERSED.)
       IDENTIFICATION DIVISION.
       PROGRAM-ID. UOPNREVX.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F3 ASSIGN TO "uopnrevx-f3.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS RANDOM
               RECORD KEY IS K3
               FILE STATUS IS ST3.
       DATA DIVISION.
       FILE SECTION.
       FD F3.
       01 R3.
          05 K3 PIC X(3).
          05 V3 PIC X(5).
       WORKING-STORAGE SECTION.
       01 ST3 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F3
           CLOSE F3
           DISPLAY "X01 " ST3 "|"
           OPEN INPUT F3 REVERSED
           DISPLAY "X02 REV " ST3 "|"
           STOP RUN.
