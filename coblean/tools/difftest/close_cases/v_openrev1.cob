      * OPEN INPUT ... REVERSED where the model runs it (IBM: REVERSED
      * does not apply to a direct-access device, Language Reference
      * 6.4, OPEN statement): an empty file and a file of one record
      * (00, read as by OPEN INPUT), an absent OPTIONAL file (05, the
      * first READ at end), an open file (41), a file closed WITH LOCK
      * (38); F4 has no FILE STATUS. Every line agrees with GnuCOBOL 3.2
      * (which ignores REVERSED; its compiler takes REVERSED only after
      * the last file of an OPEN, so each OPEN here names one file).
      * ABSENT: 3
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VOPNREV1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "vopnrev1-f1.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
           SELECT F2 ASSIGN TO "vopnrev1-f2.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST2.
           SELECT OPTIONAL F3 ASSIGN TO "vopnrev1-absent.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST3.
           SELECT F4 ASSIGN TO "vopnrev1-f4.dat"
               ORGANIZATION IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       FD F2.
       01 R2 PIC X(8).
       FD F3.
       01 R3 PIC X(8).
       FD F4.
       01 R4 PIC X(8).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       01 ST2 PIC XX VALUE "..".
       01 ST3 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F1 F2 F4
           MOVE "ONLY1XXX" TO R2 R4
           WRITE R2
           WRITE R4
           CLOSE F1 F2 F4
           DISPLAY "A01 " ST1 " " ST2 "|"
           OPEN INPUT F1 REVERSED
           DISPLAY "A02 EMPTY REV " ST1 "|"
           READ F1
           DISPLAY "A03 " ST1 "|"
           OPEN INPUT F2 REVERSED
           OPEN INPUT F4 REVERSED
           DISPLAY "A04 ONE REV " ST2 "|"
           READ F2
           DISPLAY "A05 " ST2 " " R2 "|"
           READ F2
           DISPLAY "A06 " ST2 "|"
           READ F4 AT END DISPLAY "A07 END"
           END-READ
           DISPLAY "A08 " R4 "|"
           OPEN INPUT F2 REVERSED
           DISPLAY "A09 OPEN REV " ST2 "|"
           CLOSE F2 F4
           OPEN INPUT F3 REVERSED
           DISPLAY "B01 ABSENT REV " ST3 "|"
           READ F3
           DISPLAY "B02 " ST3 "|"
           CLOSE F3
           DISPLAY "B03 " ST3 "|"
           CLOSE F1 WITH LOCK
           DISPLAY "C01 LOCK " ST1 "|"
           OPEN INPUT F1 REVERSED
           DISPLAY "C02 LOCKED REV " ST1 "|"
           STOP RUN.
