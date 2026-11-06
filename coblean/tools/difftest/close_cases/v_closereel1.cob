      * CLOSE ... REEL / UNIT on sequential disk files (IBM: a non-reel/
      * unit file; Language Reference 6.4, CLOSE statement, Tables 34,
      * 35, 38): 07, the file stays open, READs and WRITEs go on where
      * they were, a REWRITE right after gets 43, a closed file 42; F2
      * has no FILE STATUS (07 is a success: no abend). Every line
      * agrees with GnuCOBOL 3.2.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCLREEL1.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT F1 ASSIGN TO "vclreel1-f1.dat"
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS ST1.
           SELECT F2 ASSIGN TO "vclreel1-f2.dat"
               ORGANIZATION IS SEQUENTIAL.
       DATA DIVISION.
       FILE SECTION.
       FD F1.
       01 R1 PIC X(8).
       FD F2.
       01 R2 PIC X(8).
       WORKING-STORAGE SECTION.
       01 ST1 PIC XX VALUE "..".
       PROCEDURE DIVISION.
       M0.
           OPEN OUTPUT F1 F2
           DISPLAY "A01 " ST1 "|"
           MOVE "REC1XXXX" TO R1 R2
           WRITE R1
           WRITE R2
           CLOSE F1 REEL F2 UNIT
           DISPLAY "A02 REEL " ST1 "|"
           MOVE "REC2XXXX" TO R1 R2
           WRITE R1
           WRITE R2
           DISPLAY "A03 " ST1 "|"
           CLOSE F1 UNIT FOR REMOVAL
           DISPLAY "A04 REMOVAL " ST1 "|"
           CLOSE F1 REEL NO REWIND
           DISPLAY "A05 NO REWIND " ST1 "|"
           MOVE "REC3XXXX" TO R1
           WRITE R1
           DISPLAY "A06 " ST1 "|"
           CLOSE F1 F2
           DISPLAY "A07 " ST1 "|"
           CLOSE F1 REEL
           DISPLAY "A08 CLOSED " ST1 "|"
           CLOSE F1 UNIT REMOVAL
           DISPLAY "A09 CLOSED " ST1 "|"
           OPEN INPUT F1 F2
           DISPLAY "B01 " ST1 "|"
           READ F1
           DISPLAY "B02 " ST1 " " R1 "|"
           CLOSE F1 UNIT F2 REEL WITH NO REWIND
           DISPLAY "B03 UNIT " ST1 "|"
           READ F1
           DISPLAY "B04 " ST1 " " R1 "|"
           READ F2 AT END DISPLAY "B05 END"
           END-READ
           DISPLAY "B06 " R2 "|"
           READ F1
           DISPLAY "B07 " ST1 " " R1 "|"
           READ F1
           DISPLAY "B08 " ST1 " " R1 "|"
           CLOSE F1 REEL
           DISPLAY "B09 REEL AT END " ST1 "|"
           READ F1
           DISPLAY "B10 " ST1 " " R1 "|"
           CLOSE F1 F2
           DISPLAY "B11 " ST1 "|"
           OPEN I-O F1
           DISPLAY "C01 " ST1 "|"
           READ F1
           DISPLAY "C02 " ST1 " " R1 "|"
           CLOSE F1 REEL
           DISPLAY "C03 REEL " ST1 "|"
           MOVE "RWR1XXXX" TO R1
           REWRITE R1
           DISPLAY "C04 REWRITE " ST1 "|"
           READ F1
           DISPLAY "C05 " ST1 " " R1 "|"
           MOVE "RWR2XXXX" TO R1
           REWRITE R1
           DISPLAY "C06 REWRITE " ST1 "|"
           CLOSE F1 UNIT REMOVAL
           DISPLAY "C07 REMOVAL " ST1 "|"
           CLOSE F1
           DISPLAY "C08 " ST1 "|"
           OPEN EXTEND F1
           DISPLAY "D01 " ST1 "|"
           CLOSE F1 UNIT
           DISPLAY "D02 UNIT " ST1 "|"
           MOVE "REC4XXXX" TO R1
           WRITE R1
           DISPLAY "D03 " ST1 "|"
           CLOSE F1
           OPEN INPUT F1
           PERFORM 5 TIMES
             READ F1
             DISPLAY "E01 " ST1 " " R1 "|"
           END-PERFORM
           CLOSE F1
           DISPLAY "E02 " ST1 "|"
           STOP RUN.
