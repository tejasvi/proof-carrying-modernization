      * G-lockclose, sequential file: a CLOSE of a file closed WITH LOCK.
      * IBM: 42 (the file is not in an open mode; Language Reference
      * 6.4, CLOSE statement, Table 34) and the file stays locked, so the
      * OPEN after it gets 38. GnuCOBOL 3.2: L02 00, the lock is lifted,
      * L03 00 and the file is open. The lines from L02 on differ;
      * closetest.py does not generate this case.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. GLOCKCLS.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "glockcls-f1.dat"
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
           CLOSE F1 WITH LOCK
           DISPLAY "L01 LOCK " ST1 "|"
           CLOSE F1
           DISPLAY "L02 CLOSE AGAIN " ST1 "|"
           OPEN OUTPUT F1
           DISPLAY "L03 OPEN " ST1 "|"
           STOP RUN.
