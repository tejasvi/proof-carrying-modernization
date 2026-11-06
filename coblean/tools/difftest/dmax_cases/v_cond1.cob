       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCOND1.
      * dmax-fix stage B: IBM's dmax in conditions (PG "Arithmetic
      * expressions in nonarithmetic statements"): an explicit relation
      * takes the most places of any operand of either comparand
      * (divisors and exponents excluded); a sign condition and an
      * EVALUATE subject / object are evaluated on their own.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       77 A    PIC 9(3) VALUE 5.
       77 C    PIC 9(3) VALUE 3.
       77 D2   PIC S9V99 VALUE 1.00.
       77 SA   PIC S9(3) VALUE -5.
       77 N7   PIC 9 VALUE 7.
       77 K    PIC 99 VALUE 0.
       PROCEDURE DIVISION.
      * dmax 1 (1.5): 5 / 3 = 1.6 > 1.5
           IF A / C > 1.5
              DISPLAY 'C01 Y|' ELSE DISPLAY 'C01 N|' END-IF.
      * dmax 1 (1.6): 1.6 = 1.6
           IF A / C = 1.6
              DISPLAY 'C02 Y|' ELSE DISPLAY 'C02 N|' END-IF.
      * dmax 2 (D2): 1.00 / 3 = 0.33
           IF D2 / C = 0.33
              DISPLAY 'C03 Y|' ELSE DISPLAY 'C03 N|' END-IF.
      * dmax 3 (the literal 0.333): 0.333
           IF D2 / C = 0.333
              DISPLAY 'C04 Y|' ELSE DISPLAY 'C04 N|' END-IF.
      * the comparand on the left, dmax 2: 1.66 < 1.66 is false
           IF 1.66 < A / C
              DISPLAY 'C05 Y|' ELSE DISPLAY 'C05 N|' END-IF.
      * sign condition, own dmax 0: -5 / 3 = -1
           IF SA / C IS NEGATIVE
              DISPLAY 'C06 Y|' ELSE DISPLAY 'C06 N|' END-IF.
      * sign condition, own dmax 2 (D2): 1.00 / 7 = 0.14
           IF D2 / N7 IS POSITIVE
              DISPLAY 'C07 Y|' ELSE DISPLAY 'C07 N|' END-IF.
      * abbreviated relation: each part with dmax 1
           IF A / C > 1.5 AND < 1.7
              DISPLAY 'C08 Y|' ELSE DISPLAY 'C08 N|' END-IF.
      * EVALUATE TRUE with an explicit relation: dmax 1
           EVALUATE TRUE
             WHEN A / C = 1.6 DISPLAY 'C09 Y|'
             WHEN OTHER DISPLAY 'C09 N|'
           END-EVALUATE.
      * PERFORM UNTIL, dmax 1: K / 3 is 1.0, 1.3, 1.6: ends at K 5
           MOVE 0 TO K.
           PERFORM UNTIL K / 3 > 1.3
              ADD 1 TO K
           END-PERFORM.
           DISPLAY 'C10 ' K '|'.
      * EVALUATE whose subject has as many places as its object:
      * own dmax 2 = the relation's
           EVALUATE D2 / C
             WHEN 0.33 DISPLAY 'C11 W1|'
             WHEN OTHER DISPLAY 'C11 O|'
           END-EVALUATE.
           STOP RUN.
