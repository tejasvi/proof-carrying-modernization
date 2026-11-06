       IDENTIFICATION DIVISION.
       PROGRAM-ID. P3C.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R1.
           05  A        PIC X(3) VALUE 'abc'.
           05  B.
               10 B1    PIC 9(2) VALUE 12.
               10 B2    PIC X(2) VALUE 'xy'.
           05  C        PIC S9(3) COMP-3 VALUE -42.
           05  D        PIC X(4) VALUE 'dddd'.
       66  RAB RENAMES A THRU B.
       66  RB1 RENAMES B1.
       66  RB  RENAMES B.
       66  RBD RENAMES B2 THRU D.
       01  LNS.
           05  LN1 PIC 9(4).
           05  LN2 PIC 9(4).
           05  LN3 PIC 9(4).
       01  R2.
           05  A        PIC X(3) VALUE 'ABC'.
           05  E        PIC X(2) VALUE 'EE'.
       66  RB1 RENAMES E.
       PROCEDURE DIVISION.
       P0.
           DISPLAY 'RAB=' RAB '.'.
           DISPLAY 'RB1=' RB1 OF R1 '.'.
           ADD 5 TO RB1 OF R1.
           DISPLAY 'B1=' B1 '.'.
           MOVE 'zz' TO RB.
           DISPLAY 'R1=' RAB '.'.
           MOVE 'QQQQQQQQQ' TO RBD.
           DISPLAY 'D=' D ' B2=' B2 '.'.
           MOVE LENGTH OF RAB TO LN1 MOVE LENGTH OF RBD TO LN2
           MOVE LENGTH OF RB TO LN3
           DISPLAY "LEN " LN1 " " LN2 " " LN3.
           MOVE 'xx' TO RB1 OF R2.
           DISPLAY 'R2=' R2 '.'.
           STOP RUN.
