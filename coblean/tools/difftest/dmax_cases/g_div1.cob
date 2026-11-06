       IDENTIFICATION DIVISION.
       PROGRAM-ID. GDIV1.
      * G-osvsdiv: GnuCOBOL -std=ibm (arithmetic-osvs) keeps more places
      * for a quotient than IBM's rule max(d2 - d1, dmax) in these
      * shapes. Model: IBM.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A1   PIC 9V9 VALUE 1.0.
       77 B3   PIC 9V999 VALUE 3.000.
       77 X2   PIC 9(5)V99 VALUE 0.
       77 E2   PIC Z(4)9.99.
       77 D2   PIC 9V99 VALUE 1.23.
       77 N7   PIC 9 VALUE 7.
       77 Y    PIC 9(5)V99 VALUE 0.
       77 P2   PIC 9PP VALUE 300.
       77 X1   PIC 9(5)V9 VALUE 0.
       77 E1   PIC Z(4)9.9.
       PROCEDURE DIVISION.
      * divisor with 3 places, dmax 2: max(1 - 3, 2) = 2 places:
      * 0.33 * 30 = 9.90 (GnuCOBOL 9.99)
           COMPUTE X2 = A1 / B3 * 30.
           MOVE X2 TO E2.
           DISPLAY 'G01 [' E2 ']|'.
      * nested, dmax 2: 1.23 / 7 = 0.17, 0.17 / 7 = 0.02, * 1000 = 20.00
           COMPUTE Y = D2 / N7 / N7 * 1000.
           MOVE Y TO E2.
           DISPLAY 'G02 [' E2 ']|'.
      * a divisor scaled by P (9PP: no decimal places), dmax 1: 1 place:
      * 7 / 300 = 0.0, * 1000 = 0.0 (GnuCOBOL 23.3)
           COMPUTE X1 = N7 / P2 * 1000.
           MOVE X1 TO E1.
           DISPLAY 'G03 [' E1 ']|'.
           STOP RUN.
