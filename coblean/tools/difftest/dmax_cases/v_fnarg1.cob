       IDENTIFICATION DIVISION.
       PROGRAM-ID. VFNARG1.
      * inr-fix (R1, F7): an expression inside a function argument is
      * computed with the function's inner-dmax (the most places of
      * its arguments) in every statement. Lines where GnuCOBOL agrees.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 D2   PIC S9V99 VALUE 1.00.
       77 D1   PIC S9V9 VALUE 1.5.
       77 X6   PIC S9(3)V9(6) VALUE 0.
       77 E6   PIC -ZZ9.9(6).
       PROCEDURE DIVISION.
      * F01 relation: D2 / D1 with MAX's 2 places, 0.66 (was 0.6)
           IF FUNCTION MAX (D2 / D1, 0.05) > 0.65
              DISPLAY 'F01 Y' ELSE DISPLAY 'F01 N' END-IF.
      * F02 sign condition: 0.66 - 0.65 is positive
           IF FUNCTION SUM (D2 / D1, -0.65) POSITIVE
              DISPLAY 'F02 Y' ELSE DISPLAY 'F02 N' END-IF.
      * F03 abbreviated relation, each relation as written: 0.66
           IF FUNCTION MAX (D2 / D1, 0.05) > 0.6 AND < 0.67
              DISPLAY 'F03 Y' ELSE DISPLAY 'F03 N' END-IF.
      * F04 NIST IF133A's REM (3 / 2, .75): 3 / 2 with the 2 places
      * of .75 is 1.50, the remainder 0 (with 0 places 0.25)
           COMPUTE X6 = FUNCTION REM (3 / 2, .75).
           MOVE X6 TO E6.
           DISPLAY 'F04 ' E6.
           STOP RUN.
