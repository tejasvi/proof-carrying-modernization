       IDENTIFICATION DIVISION.
       PROGRAM-ID. GFNARG1.
      * inr-fix (R1): GnuCOBOL departs (G-fnarg). It keeps more places
      * for a quotient inside a function argument than IBM's
      * inner-dmax, the most places of the function's arguments.
      * Model (IBM): G01 0.140000, G02 1.140000, G03 0.046666,
      * G04 2.800000, G05 W.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 D2   PIC S9V99 VALUE 1.00.
       77 D1   PIC S9V9 VALUE 1.5.
       77 N7   PIC 9 VALUE 7.
       77 X6   PIC S9(3)V9(6) VALUE 0.
       77 E6   PIC -ZZ9.9(6).
       PROCEDURE DIVISION.
      * G01 the receiver's 6 places do not reach the argument
           COMPUTE X6 = FUNCTION MAX (D2 / N7, 0.05).
           MOVE X6 TO E6.
           DISPLAY 'G01 ' E6.
      * G02 nor does ROUNDED
           COMPUTE X6 ROUNDED = FUNCTION SUM (D2 / N7, 1).
           MOVE X6 TO E6.
           DISPLAY 'G02 ' E6.
      * G03 a quotient outside the arguments divides MAX's 0.14
           COMPUTE X6 = FUNCTION MAX (D2 / N7, 0.05) / 3.
           MOVE X6 TO E6.
           DISPLAY 'G03 ' E6.
      * G04 nested functions: 7 / 3 with the 1 place of SUM's 0.5
           COMPUTE X6 = FUNCTION MAX (FUNCTION SUM (N7 / 3, 0.5), D2).
           MOVE X6 TO E6.
           DISPLAY 'G04 ' E6.
      * G05 an EVALUATE subject: MAX is 0.66
           EVALUATE FUNCTION MAX (D2 / D1, 0.05)
             WHEN 0.66 DISPLAY 'G05 W'
             WHEN OTHER DISPLAY 'G05 O'
           END-EVALUATE.
           STOP RUN.
