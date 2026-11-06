      * CLOSE ... WITH NO REWIND and WITH LOCK (IBM: Language Reference
      * 6.4, CLOSE statement, Tables 34-38): NO REWIND closes a
      * sequential disk file with 07; LOCK closes a sequential or an
      * indexed file (00) and every later OPEN of it gets 38 (READ 47,
      * WRITE 48 on the closed file); a closed file gets 42. F2 has no
      * FILE STATUS (07 and the lock's 00 are successes: no abend).
      * Every line agrees with GnuCOBOL 3.2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCLLOCK1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "vcllock1-f1.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
           SELECT F2 ASSIGN TO "vcllock1-f2.dat"
               ORGANIZATION IS SEQUENTIAL.
           SELECT F3 ASSIGN TO "vcllock1-f3.dat"
               ORGANIZATION IS INDEXED ACCESS MODE IS RANDOM
               RECORD KEY IS K3
               FILE STATUS IS ST3.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       FD F2.
       01 R2 PIC X(8).
       FD F3.
       01 R3.
          05 K3 PIC X(3).
          05 V3 PIC X(5).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       01 ST3 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F1 F2 F3
           DISPLAY "A01 " ST1 " " ST3 "|"
           MOVE "REC1XXXX" TO R1 R2
           WRITE R1
           WRITE R2
           MOVE "K02VAL02" TO R3
           WRITE R3
           DISPLAY "A02 " ST1 " " ST3 "|"
           CLOSE F1 WITH NO REWIND F2 NO REWIND
           DISPLAY "A03 NO REWIND " ST1 "|"
           READ F1
           DISPLAY "A04 READ " ST1 "|"
           CLOSE F1 NO REWIND
           DISPLAY "A05 CLOSED " ST1 "|"
           CLOSE F1 WITH LOCK
           DISPLAY "A06 CLOSED " ST1 "|"
           OPEN INPUT F1 F2
           DISPLAY "B01 " ST1 "|"
           READ F1
           DISPLAY "B02 " ST1 " " R1 "|"
           READ F2
           DISPLAY "B03 " R2 "|"
           CLOSE F1 WITH LOCK F2 LOCK
           DISPLAY "B04 LOCK " ST1 "|"
           OPEN INPUT F1
           DISPLAY "B05 " ST1 "|"
           OPEN OUTPUT F1
           DISPLAY "B06 " ST1 "|"
           OPEN I-O F1
           DISPLAY "B07 " ST1 "|"
           OPEN EXTEND F1
           DISPLAY "B08 " ST1 "|"
           READ F1
           DISPLAY "B09 " ST1 "|"
           MOVE "REC2XXXX" TO R1
           WRITE R1
           DISPLAY "B10 " ST1 "|"
           CLOSE F3 LOCK
           DISPLAY "C01 LOCK " ST3 "|"
           OPEN INPUT F3
           DISPLAY "C02 " ST3 "|"
           OPEN I-O F3
           DISPLAY "C03 " ST3 "|"
           OPEN OUTPUT F3
           DISPLAY "C04 " ST3 "|"
           MOVE "K02" TO K3
           READ F3
           DISPLAY "C05 " ST3 "|"
           MOVE "K05VAL05" TO R3
           WRITE R3
           DISPLAY "C06 " ST3 "|"
           STOP RUN.
