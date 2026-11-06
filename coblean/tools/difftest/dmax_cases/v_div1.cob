       IDENTIFICATION DIVISION.
       PROGRAM-ID. VDIV1.
      * dmax-fix stage E: a quotient carries "(d2 - d1) or dmax,
      * whichever is greater" decimal places (IBM; d2 the dividend's,
      * d1 the divisor's); GnuCOBOL -std=ibm agrees in these cases.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A    PIC 9(3) VALUE 2.
       77 B3   PIC 9V999 VALUE 3.000.
       77 C    PIC 9(3) VALUE 3.
       77 X0   PIC 9(5) VALUE 0.
       77 D2   PIC 9V99 VALUE 1.23.
       77 F2   PIC 9V99 VALUE 4.56.
       77 N7   PIC 9 VALUE 7.
       77 Y    PIC 9(5)V99 VALUE 0.
       77 E2   PIC Z(4)9.99.
       77 X1   PIC 9(5)V9 VALUE 0.
       77 E1   PIC Z(4)9.9.
       PROCEDURE DIVISION.
      * max(0 - 3, 0) = 0 places: 2 / 3 = 0, * 3 = 0
           COMPUTE X0 = A / B3 * C.
           DISPLAY 'Q01 ' X0 '|'.
      * a product dividend: d2 4, d1 0, dmax 2: 4 places,
      * 5.6088 / 7 = 0.8012, * 100 = 80.12
           COMPUTE Y = D2 * F2 / N7 * 100.
           MOVE Y TO E2.
           DISPLAY 'Q02 [' E2 ']|'.
      * one division alone (CBACT04C's shape): 0.0046 stored as 0.00
           COMPUTE Y = D2 * F2 / 1200.
           MOVE Y TO E2.
           DISPLAY 'Q03 [' E2 ']|'.
      * ROUNDED: max(0, 1) + 1 = 2 places: 2.33 * 3 = 6.99, 7.0
           COMPUTE X1 ROUNDED = N7 / C * 3.
           MOVE X1 TO E1.
           DISPLAY 'Q04 [' E1 ']|'.
           STOP RUN.
