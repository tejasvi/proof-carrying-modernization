       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPOWND.
      * G-pownegdiv: for a negative exponent IBM divides 1 by ir4 (the
      * power truncated to dmax places) and keeps dmax places (ir5);
      * GnuCOBOL divides 1 by the exact power. Every U line differs.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  THREE  PIC 9 VALUE 3.
       77  TWO    PIC 9 VALUE 2.
       77  NM     PIC S9 VALUE -1.
       77  NM2    PIC S9 VALUE -2.
       77  NM3    PIC S9 VALUE -3.
       77  DC     PIC 9V9 VALUE 0.3.
       77  DT     PIC 9V99 VALUE 0.01.
       77  W0     PIC S9(5) VALUE 0.
       77  W2     PIC S9(3)V99 VALUE 0.
       77  W6     PIC S9(7)V99 VALUE 0.
       77  E0     PIC -(5)9.
       77  E2     PIC -(3)9.99.
       77  E6     PIC -(7)9.99.
       PROCEDURE DIVISION.
      * dmax 2: ir4 0.02, ir5 50.00 (GnuCOBOL 1 / 0.027 = 37.03)
           COMPUTE W2 = DC ** NM3.
           MOVE W2 TO E2. DISPLAY 'U01 [' E2 ']'.
      * dmax 0: ir5 0, so 0 (GnuCOBOL 1 / 3 * 9 = 2)
           COMPUTE W0 = THREE ** NM * 9.
           MOVE W0 TO E0. DISPLAY 'U02 [' E0 ']'.
      * dmax 0 in the relation: ir5 0 = 0 (GnuCOBOL 0.5)
           IF TWO ** NM = 0 DISPLAY 'U03 Y|' ELSE DISPLAY 'U03 N|'.
      * dmax 2: ir4 0.00, so 1 / ir4 is a size error (GnuCOBOL
      * 1 / 0.0001 = 10000.00)
           MOVE 77 TO W6.
           COMPUTE W6 = DT ** NM2
               ON SIZE ERROR DISPLAY 'U04 Z|'
               NOT ON SIZE ERROR DISPLAY 'U04 N|'
           END-COMPUTE.
           MOVE W6 TO E6. DISPLAY 'U05 [' E6 ']'.
           STOP RUN.
