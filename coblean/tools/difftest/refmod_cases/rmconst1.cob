      * Reference modifiers that are arithmetic expressions of integer
      * literals and at most one integer name (IBM: leftmost-character-
      * position and length "Must be an arithmetic expression"): the front
      * end evaluates them exactly to a literal or name + k.
      * Run: filetest.py --run rmconst1.cob (both sides, line by line).
      * Control: the front end of coblean-20261027T0518Z makes these
      * statements unsupported ("not of the form literal / name [+|-
      * integer]"). Planted fault (recipe): in parser.py sub_of's linear(),
      * return (a[0], a[1] + c[1]) also for "-" (minus read as plus).
       IDENTIFICATION DIVISION.
       PROGRAM-ID. RMC1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  T1 PIC X(10) VALUE 'ABCDEFGHIJ'.
       01  N1 PIC 9(9) VALUE 123456789.
       01  G1.
           05 G1A PIC X(4) VALUE 'KLMN'.
           05 G1B PIC 9(4) VALUE 4321.
       01  TB.
           05 TE OCCURS 3 PIC X(5).
       01  I PIC 99 VALUE 2.
       01  J PIC S9(3) COMP VALUE 3.
       01  R PIC X(10).
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE 'AAAAABBBBBCCCCC' TO TB
           DISPLAY '1 [' T1 (10 - 7: 6 + 2 - 5) ']'
           DISPLAY '2 [' T1 (2 * 3:) ']'
           DISPLAY '3 [' T1 ((1 + 1) * 2: 10 - 2 * 4) ']'
           DISPLAY '4 [' T1 (- 2 + 5: + 2) ']'
           DISPLAY '5 [' N1 (10 - 7: 6 + 2 - 5) ']'
           DISPLAY '6 [' G1 (3 + 1: 7 - 3 - 1) ']'
           DISPLAY '7 [' TE (2) (5 - 3: 2 * 1 + 1) ']'
           DISPLAY '8 [' T1 (I + 3 - 1: 2 * 2) ']'
           DISPLAY '9 [' T1 (3 + I:) ']'
           DISPLAY '10 [' T1 (J - 1 - 1: (J + 1) - 2) ']'
           IF T1 (10 - 7: 6 + 2 - 5) = 'CDE'
              DISPLAY '11 EQUAL' ELSE DISPLAY '11 NOT EQUAL' END-IF
           IF N1 (10 - 7: 6 + 2 - 5) = 345
              DISPLAY '12 EQUAL' ELSE DISPLAY '12 NOT EQUAL' END-IF
           MOVE ALL '*' TO R
           MOVE T1 (12 - 4: 3 * 1) TO R (9 - 6: 2 + 2)
           DISPLAY '13 [' R ']'
           MOVE 'XYZ' TO T1 (I + 0: 4 - 1)
           DISPLAY '14 [' T1 ']'
           STOP RUN.
