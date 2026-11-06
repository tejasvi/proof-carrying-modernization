      * BY CONTENT items and literals, ON EXCEPTION / NOT ON EXCEPTION of nested programs,
      * CALL identifier with a longer item, the same item twice BY REFERENCE (one storage).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q11.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 A1 PIC 99 VALUE 5.
       01 A2 PIC 99 VALUE 7.
       01 PN PIC X(8) VALUE 'Q11B'.
       PROCEDURE DIVISION.
           DISPLAY 'START'.
           CALL 'Q11B' USING A1 A1.
           DISPLAY 'M1 ' A1.
           CALL PN USING A1 A2.
           DISPLAY 'M2 ' A1 ' ' A2.
           CALL PN USING A2 A2.
           DISPLAY 'M3 ' A1 ' ' A2.
           STOP RUN.
       END PROGRAM Q11.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. Q11B.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 CNT PIC 99 VALUE 0.
       LINKAGE SECTION.
       01 P1 PIC 99.
       01 P2 PIC 99.
          88 P2-BIG VALUE 20 THRU 99.
       PROCEDURE DIVISION USING P1 P2.
           ADD 1 TO CNT.
           ADD 10 TO P1.
           DISPLAY 'B ' CNT ' ' P1 ' ' P2.
           IF P2-BIG DISPLAY 'BIG' END-IF.
           ADD 1 TO P2.
           DISPLAY 'B ' P1 ' ' P2.
           PERFORM X.
           EXIT PROGRAM.
       X.
           DISPLAY 'X ' P2.
       END PROGRAM Q11B.
