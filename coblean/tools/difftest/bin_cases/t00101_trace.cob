       IDENTIFICATION DIVISION.
       PROGRAM-ID. T00101.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 N2 PIC S9(5)V9(3) COMP-5 VALUE 56600.627.
          05 A3 PIC X(5) VALUE 'XKFKL'.
          05 N4 PIC 9(7)V9(2) COMP-3 VALUE 4340506.11.
          05 E5 PIC ZZZZ9 VALUE ZERO.
          05 A6 PIC X(2) VALUE '9C'.
          05 E7 PIC 99/99/99 VALUE ZERO.
          05 N8 PIC S9(2)V9(1) VALUE 37.9.
          05 A9 PIC X(8) VALUE 'M2K IXDA'.
          05 FLAG PIC X(1) VALUE 'N'.
       01 RX REDEFINES R.
          05 BYTE PIC X OCCURS 41.
       01 IDX PIC 9(4) COMP.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MULTIPLY N2 BY N4 ROUNDED MODE NEAREST-TOWARD-ZERO
           END-MULTIPLY
           DISPLAY "S" N2 "|" N4 "|" N8
           DIVIDE N4 BY N4 GIVING N8
           ON SIZE ERROR MOVE 'E' TO FLAG NOT ON SIZE ERROR MOVE 'K' TO
           FLAG
           END-DIVIDE
           DISPLAY "S" N2 "|" N4 "|" N8
           DIVIDE N8 BY N4 GIVING N8 ROUNDED MODE NEAREST-AWAY-FROM-ZERO
           ON SIZE ERROR MOVE 'E' TO FLAG NOT ON SIZE ERROR MOVE 'K' TO
           FLAG
           END-DIVIDE
           DISPLAY "S" N2 "|" N4 "|" N8
           MULTIPLY N4 BY N8 ROUNDED
           END-MULTIPLY
           DISPLAY "S" N2 "|" N4 "|" N8
           SUBTRACT N4 FROM N2 ROUNDED
           END-SUBTRACT
           DISPLAY "S" N2 "|" N4 "|" N8
           DIVIDE N8 INTO N8 ROUNDED MODE TRUNCATION
           ON SIZE ERROR MOVE 'E' TO FLAG NOT ON SIZE ERROR MOVE 'K' TO
           FLAG
           END-DIVIDE
           DISPLAY "S" N2 "|" N4 "|" N8
           ADD N4 N2 TO N8
           END-ADD
           DISPLAY "S" N2 "|" N4 "|" N8
           ADD N2 TO N4 N8 ROUNDED
           END-ADD
           DISPLAY "S" N2 "|" N4 "|" N8
           IF N4 = N4
           MOVE 'Y' TO FLAG
           ELSE
           MOVE 'N' TO FLAG
           END-IF
           DISPLAY "S" N2 "|" N4 "|" N8
           PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 41
              DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING
           END-PERFORM
           DISPLAY ' '
           STOP RUN.
