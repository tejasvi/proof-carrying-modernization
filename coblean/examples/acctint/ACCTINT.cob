       IDENTIFICATION DIVISION.
       PROGRAM-ID. ACCTINT.
      * Accrue simple daily interest on one account record.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       COPY ACCTREC.
       01  WS-WORK.
           05  WS-INTEREST      PIC S9(9)V99  COMP-3 VALUE ZERO.
           05  WS-DAILY-RATE    PIC S9V9(8)   COMP-3 VALUE ZERO.
           05  WS-STATUS        PIC X              VALUE SPACE.
               88  WS-OK                           VALUE 'K'.
               88  WS-OVERFLOW                     VALUE 'E'.
               88  WS-SKIPPED                      VALUE 'Z'.
       PROCEDURE DIVISION.
       0000-MAIN.
           PERFORM 1000-CALC THRU 1000-EXIT.
           GOBACK.
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
