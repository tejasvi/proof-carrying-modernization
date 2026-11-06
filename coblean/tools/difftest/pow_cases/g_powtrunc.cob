       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPOWTR.
      * G-powtrunc: IBM moves the power to an intermediate result of
      * dmax decimal places (ir4) before using it; GnuCOBOL keeps
      * every place of the exact power. Every T line differs: the
      * model gives IBM's value.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  THREE  PIC 9 VALUE 3.
       77  DA     PIC S9V9 VALUE 1.5.
       77  DH     PIC 9V9 VALUE 0.5.
       77  W0     PIC S9(5) VALUE 0.
       77  W1     PIC S9(5)V9 VALUE 0.
       77  E0     PIC -(5)9.
       77  E1     PIC -(5)9.9.
       PROCEDURE DIVISION.
      * dmax 1: ir4 3.3, so 33.0 (GnuCOBOL 3.375 * 10 = 33.7)
           COMPUTE W1 = DA ** THREE * 10.
           MOVE W1 TO E1. DISPLAY 'T01 [' E1 ']'.
      * dmax 1: 3.3 + 3.3 = 6.6 (GnuCOBOL 6.75: 6.7)
           COMPUTE W1 = DA ** THREE + DA ** THREE.
           MOVE W1 TO E1. DISPLAY 'T02 [' E1 ']'.
      * dmax 1: ir4 0.2, so 20 (GnuCOBOL 0.25 * 100 = 25)
           COMPUTE W0 = DH ** TWO * 100.
           MOVE W0 TO E0. DISPLAY 'T03 [' E0 ']'.
      * dmax 1: inner ir4 2.2, outer 4.84: 4.8 (GnuCOBOL 5.0625: 5.0)
           COMPUTE W1 = (DA ** TWO) ** TWO.
           MOVE W1 TO E1. DISPLAY 'T04 [' E1 ']'.
           STOP RUN.
