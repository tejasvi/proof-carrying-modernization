       IDENTIFICATION DIVISION.
       PROGRAM-ID. T00197.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N2 PIC S9(6)V9(1) COMP-5 VALUE 938986.4.
          05 A3 PIC X(6) VALUE 'TNWECP'.
          05 E4 PIC 9B999 VALUE ZERO.
          05 N5 PIC S9(6)V9(3) COMP-3 VALUE 284683.386.
          05 E6 PIC ZZ9.99- VALUE ZERO.
          05 N7 PIC V9(3) COMP-5 VALUE 0.889.
          05 FLAG PIC X(1) VALUE 'N'.
       01 RX REDEFINES R.
          05 BYTE PIC X OCCURS 30.
       01 IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           IF FLAG < A3
           MOVE 'Y' TO FLAG
           ELSE
           MOVE 'N' TO FLAG
           END-IF
           MULTIPLY N2 BY N2 ROUNDED MODE NEAREST-EVEN
           END-MULTIPLY
           ADD N7 N2 TO N5
           ON SIZE ERROR MOVE 'E' TO FLAG NOT ON SIZE ERROR MOVE 'K' TO
           FLAG
           END-ADD
           IF N7 <> N5
           MOVE 'Y' TO FLAG
           ELSE
           MOVE 'N' TO FLAG
           END-IF
           IF A3 < A3
           MOVE 'Y' TO FLAG
           ELSE
           MOVE 'N' TO FLAG
           END-IF
           SUBTRACT N2 FROM N5
           ON SIZE ERROR MOVE 'E' TO FLAG NOT ON SIZE ERROR MOVE 'K' TO
           FLAG
           END-SUBTRACT
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 30
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
