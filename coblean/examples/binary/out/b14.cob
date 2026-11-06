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
       01  WS-BYTES REDEFINES WS-REC.
           05 WS-B PIC X OCCURS 8.
       01  BX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       DRIVER.
           MOVE FUNCTION CHAR(256) TO WS-B(1)
           MOVE FUNCTION CHAR(256) TO WS-B(2)
           MOVE FUNCTION CHAR(256) TO WS-B(3)
           MOVE FUNCTION CHAR(256) TO WS-B(4)
           MOVE FUNCTION CHAR(256) TO WS-B(5)
           MOVE FUNCTION CHAR(128) TO WS-B(6)
           MOVE FUNCTION CHAR(118) TO WS-B(7)
           MOVE FUNCTION CHAR(91) TO WS-B(8)
           PERFORM 0000-MAIN
           PERFORM VARYING BX FROM 1 BY 1 UNTIL BX > 8
              DISPLAY FUNCTION ORD(WS-B(BX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
       0000-MAIN.
           ADD 1 TO WS-CNT.
           COMPUTE WS-TOTAL = WS-TOTAL + WS-CNT * 3.
           MOVE WS-HI TO WS-OUT.
           EXIT.
