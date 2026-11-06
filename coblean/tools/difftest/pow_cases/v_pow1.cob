       IDENTIFICATION DIVISION.
       PROGRAM-ID. VPOW1.
      * Exponents that are integral data items or expressions (IBM:
      * fixed point, the power held with dmax decimal places): cases
      * where GnuCOBOL computes IBM's result (powtest.py --run).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77  TWO    PIC 9 VALUE 2.
       77  THREE  PIC 9 VALUE 3.
       77  TEN    PIC 99 VALUE 10.
       77  ATWO   PIC S9 VALUE 2.
       77  NM     PIC S9 VALUE -1.
       77  NZ     PIC 9 VALUE 0.
       77  NC3    PIC S9 COMP-3 VALUE 3.
       77  NB4    PIC S9(4) COMP VALUE 4.
       77  IA     PIC S99 VALUE -3.
       77  DA     PIC S9V9 VALUE 1.5.
       77  DH     PIC 9V9 VALUE 0.5.
       77  W5     PIC S9(5) VALUE 0.
       77  R2     PIC S9(5)V99 VALUE 0.
       77  R4     PIC S9(3)V9(4) VALUE 0.
       77  E5     PIC -(5)9.
       77  E2     PIC -(5)9.99.
       77  E4     PIC -(3)9.9(4).
       PROCEDURE DIVISION.
      * NC250A and NC252A shapes
           IF 1000 LESS THAN 10 ** THREE + 1
               DISPLAY 'P01 Y|' ELSE DISPLAY 'P01 N|'.
           IF 1000 NOT GREATER THAN 10 ** THREE - 1
               DISPLAY 'P02 Y|' ELSE DISPLAY 'P02 N|'.
           IF 9 ** TWO + (180 - 90) IS NOT POSITIVE
               DISPLAY 'P03 Y|' ELSE DISPLAY 'P03 N|'.
           IF 10 ** THREE + 99 - (1500 - 400) IS NEGATIVE
               DISPLAY 'P04 Y|' ELSE DISPLAY 'P04 N|'.
           COMPUTE W5 = 3 ** ATWO.
           MOVE W5 TO E5. DISPLAY 'P05 [' E5 ']'.
      * exponent forms: items of every usage, sums, negation, zero
           COMPUTE W5 = IA ** THREE.
           MOVE W5 TO E5. DISPLAY 'P06 [' E5 ']'.
           COMPUTE W5 = IA ** (THREE + 1).
           MOVE W5 TO E5. DISPLAY 'P07 [' E5 ']'.
           COMPUTE W5 = TEN ** (- NM).
           MOVE W5 TO E5. DISPLAY 'P08 [' E5 ']'.
           COMPUTE W5 = IA ** NZ.
           MOVE W5 TO E5. DISPLAY 'P09 [' E5 ']'.
           COMPUTE W5 = TWO ** (NC3 * 2).
           MOVE W5 TO E5. DISPLAY 'P10 [' E5 ']'.
           COMPUTE W5 = TWO ** (NB4 - NC3).
           MOVE W5 TO E5. DISPLAY 'P11 [' E5 ']'.
           COMPUTE W5 = TWO ** NB4 * 10.
           MOVE W5 TO E5. DISPLAY 'P12 [' E5 ']'.
      * decimal bases whose powers keep every place within dmax
           COMPUTE R4 = DA ** THREE.
           MOVE R4 TO E4. DISPLAY 'P13 [' E4 ']'.
           COMPUTE R2 = DH ** TWO.
           MOVE R2 TO E2. DISPLAY 'P14 [' E2 ']'.
           COMPUTE R2 = DA ** TWO + DA ** 2.
           MOVE R2 TO E2. DISPLAY 'P15 [' E2 ']'.
      * negative exponents with an exact quotient
           COMPUTE R2 = TWO ** NM.
           MOVE R2 TO E2. DISPLAY 'P16 [' E2 ']'.
           COMPUTE R4 = DH ** (NM * 2).
           MOVE R4 TO E4. DISPLAY 'P17 [' E4 ']'.
      * a receiver that overflows: a size error on both sides
           MOVE 77 TO W5.
           COMPUTE W5 = TEN ** (THREE * 2)
               ON SIZE ERROR DISPLAY 'P18 Z|'
               NOT ON SIZE ERROR DISPLAY 'P18 N|'
           END-COMPUTE.
           MOVE W5 TO E5. DISPLAY 'P19 [' E5 ']'.
      * a nested power, powers on both sides of a relation
           COMPUTE W5 = (TWO ** THREE) ** TWO.
           MOVE W5 TO E5. DISPLAY 'P20 [' E5 ']'.
           IF TWO ** THREE = THREE ** TWO - 1
               DISPLAY 'P21 Y|' ELSE DISPLAY 'P21 N|'.
           STOP RUN.
