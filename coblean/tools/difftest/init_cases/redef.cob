       IDENTIFICATION DIVISION.
       PROGRAM-ID. REDEF.
      * INITIALIZE of identifiers with a REDEFINES clause (IBM rule 1a:
      * identifier-1 might itself have one; items below it with or
      * under one are skipped). Before 2026-10-27 the resolver skipped
      * R1, G2, WB, VB, UB entirely. filetest.py --run: GnuCOBOL and
      * the model agree.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  R0 PIC X(6) VALUE 'ABCDEF'.
       01  R1 REDEFINES R0 PIC 9(6).
       01  G0.
           05  G0A PIC X(4) VALUE 'ABCD'.
           05  G0B PIC 9(4) VALUE 1234.
       01  G2 REDEFINES G0.
           05  G2A PIC 9(4).
           05  G2B PIC X(4).
       01  W.
           05  WA PIC X(4) VALUE 'WWWW'.
           05  WB REDEFINES WA PIC 9(4).
           05  WC PIC 9(2) VALUE 12.
       01  V.
           05  VA PIC X(4) VALUE 'VVVV'.
           05  VB REDEFINES VA.
               10  VB1 PIC 9(2).
               10  VB2 PIC X(2).
           05  VC PIC 9(2) VALUE 34.
       01  U.
           05  UA PIC X(6) VALUE 'UUUUUU'.
           05  UB REDEFINES UA.
               10  UB1 PIC 9 OCCURS 3.
               10  UB2 PIC X(3).
       PROCEDURE DIVISION.
           INITIALIZE R1
           DISPLAY 'R1 [' R0 ']'
           INITIALIZE G2
           DISPLAY 'G2 [' G0 ']'
           MOVE 'ABCD1234' TO G0
           INITIALIZE G2A
           DISPLAY 'G2A [' G0 ']'
           INITIALIZE W
           DISPLAY 'W [' W ']'
           MOVE 'WWWW12' TO W
           INITIALIZE WB
           DISPLAY 'WB [' W ']'
           INITIALIZE V
           DISPLAY 'V [' V ']'
           MOVE 'VVVV34' TO V
           INITIALIZE VB
           DISPLAY 'VB [' V ']'
           INITIALIZE UB
           DISPLAY 'UB [' U ']'
           STOP RUN.
