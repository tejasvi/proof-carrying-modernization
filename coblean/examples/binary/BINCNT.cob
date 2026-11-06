       IDENTIFICATION DIVISION.
       PROGRAM-ID. BINCNT.
      * Binary (COMP-5) counters with wrap-around, and a byte view of
      * a binary item through REDEFINES.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-REC.
           05  WS-CNT          PIC S9(4) COMP-5.
           05  WS-TOTAL        PIC S9(9) COMP-5.
           05  WS-TOTAL-X REDEFINES WS-TOTAL.
               10  WS-HI       PIC X(2).
               10  WS-LO       PIC X(2).
           05  WS-OUT          PIC X(2).
       PROCEDURE DIVISION.
       0000-MAIN.
           ADD 1 TO WS-CNT.
           COMPUTE WS-TOTAL = WS-TOTAL + WS-CNT * 3.
           MOVE WS-HI TO WS-OUT.
           GOBACK.
