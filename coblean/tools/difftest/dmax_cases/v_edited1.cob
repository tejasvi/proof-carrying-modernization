       IDENTIFICATION DIVISION.
       PROGRAM-ID. VEDITED1.
      * dmax-fix stage C: IBM's dmax of a COMPUTE counts "the number of
      * decimal places needed for the final result field or fields",
      * numeric-edited receivers included.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 TEN  PIC 99 VALUE 10.
       77 FOUR PIC 9 VALUE 4.
       77 SA   PIC S99 VALUE -7.
       77 E    PIC ZZ9.99.
       77 E3   PIC Z9.999.
       77 SE   PIC -ZZ9.99.
       77 N1   PIC 9V9.
       77 EN1  PIC 9.9.
       PROCEDURE DIVISION.
      * dmax 2 (the receiver): 10 / 4 = 2.50
           COMPUTE E = TEN / FOUR.
           DISPLAY 'D01 [' E ']|'.
      * dmax 3: 4 / 3 = 1.333
           COMPUTE E3 = FOUR / 3.
           DISPLAY 'D02 [' E3 ']|'.
      * two receivers, the edited one gives dmax 2: N1 2.5, E 2.50
           COMPUTE N1 E = TEN / FOUR.
           MOVE N1 TO EN1.
           DISPLAY 'D03 [' EN1 '] [' E ']|'.
      * a signed edited receiver: -7 / 4 = -1.75
           COMPUTE SE = SA / FOUR.
           DISPLAY 'D04 [' SE ']|'.
      * ROUNDED: dmax 2, one more place: 10 / 3 = 3.333, rounded 3.33
           COMPUTE E ROUNDED = TEN / 3.
           DISPLAY 'D05 [' E ']|'.
      * a product after the quotient: 2.50 * 3 = 7.50
           COMPUTE E = TEN / FOUR * 3.
           DISPLAY 'D06 [' E ']|'.
           STOP RUN.
