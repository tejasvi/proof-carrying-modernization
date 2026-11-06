       IDENTIFICATION DIVISION.
       PROGRAM-ID. ACCTINT.
      * Accrue simple daily interest on one account record.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
      * Account master record (copybook)
       01  ALLSTORE.
       02  ACCT-REC.
           05  ACCT-ID          PIC X(8).
           05  ACCT-TYPE        PIC X.
           05  ACCT-BALANCE     PIC S9(11)V99 COMP-3.
           05  ACCT-BAL-RAW REDEFINES ACCT-BALANCE
                                PIC X(7).
           05  ACCT-RATE        PIC SV9(5)    COMP-3.
           05  ACCT-DAYS        PIC 9(3)      COMP.
       02  WS-WORK.
           05  WS-INTEREST      PIC S9(9)V99  COMP-3 VALUE ZERO.
           05  WS-DAILY-RATE    PIC S9V9(8)   COMP-3 VALUE ZERO.
           05  WS-STATUS        PIC X              VALUE SPACE.
               88  WS-OK                           VALUE 'K'.
               88  WS-OVERFLOW                     VALUE 'E'.
               88  WS-SKIPPED                      VALUE 'Z'.
       01  DUMPV REDEFINES ALLSTORE.
           05 DBYTE PIC X OCCURS 33.
       01  DX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       0000-MAIN.
           MOVE SPACES TO ACCT-ID
           MOVE 'C' TO ACCT-TYPE
           MOVE 76702195627.37 TO ACCT-BALANCE
           MOVE 0.41458 TO ACCT-RATE
           MOVE 0 TO ACCT-DAYS
           PERFORM 1000-CALC THRU 1000-EXIT
           PERFORM VARYING DX FROM 1 BY 1 UNTIL DX > 33
              DISPLAY FUNCTION ORD(DBYTE(DX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
       DUMMY-PARA.
           CONTINUE.
       1000-CALC.
           IF ACCT-BAL-RAW = LOW-VALUES
              MOVE ZERO TO ACCT-BALANCE
           END-IF.
           IF ACCT-DAYS = 0
              OR (ACCT-TYPE NOT = 'S' AND ACCT-TYPE NOT = 'C')
              SET WS-SKIPPED TO TRUE
              GO TO 1000-EXIT
           END-IF.
           COMPUTE WS-DAILY-RATE ROUNDED = ACCT-RATE / 365.
           COMPUTE WS-INTEREST ROUNDED
                 = ACCT-BALANCE * WS-DAILY-RATE * ACCT-DAYS
              ON SIZE ERROR
                 SET WS-OVERFLOW TO TRUE
                 GO TO 1000-EXIT
           END-COMPUTE.
           ADD WS-INTEREST TO ACCT-BALANCE
              ON SIZE ERROR
                 SET WS-OVERFLOW TO TRUE
              NOT ON SIZE ERROR
                 SET WS-OK TO TRUE
           END-ADD.
       1000-EXIT.
           EXIT.
