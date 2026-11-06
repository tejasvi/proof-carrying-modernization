       IDENTIFICATION DIVISION.
       PROGRAM-ID. T00130.
      * T00130.cob (difftest.py --trunc bin --n 200 --seed 12, case 130)
      * with a DISPLAY of N4, N5, N6 after each statement and of the
      * SIZE ERROR phrase that ran.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 R.
          05 A2 PIC X(5) JUSTIFIED RIGHT VALUE 'QKJVB'.
          05 E3 PIC 99/99/99 VALUE ZERO.
          05 N4 PIC S9(5) COMP-5 VALUE 23632.
          05 N5 PIC S9(1) COMP VALUE 5.
          05 N6 PIC S9(2)V9(1) COMP-3 VALUE -88.7.
          05 A7 PIC X(6) VALUE 'SUW266'.
          05 FLAG PIC X(1) VALUE 'N'.
       PROCEDURE DIVISION.
       MAIN-PARA.
           DISPLAY "S" N4 "|" N5 "|" N6
           MOVE 1999.28 TO N5
           DISPLAY "S" N4 "|" N5 "|" N6
           ADD N5 TO N6 N4
           ON SIZE ERROR DISPLAY "SON SIZE ERROR"
           NOT ON SIZE ERROR DISPLAY "SNOT ON SIZE ERROR"
           END-ADD
           DISPLAY "S" N4 "|" N5 "|" N6
           IF A2 < A2
           MOVE 'Y' TO FLAG
           ELSE
           MOVE 'N' TO FLAG
           END-IF
           MOVE N5 TO N6
           DISPLAY "S" N4 "|" N5 "|" N6
           STOP RUN.
