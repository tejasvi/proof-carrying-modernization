      * MOVE into JUSTIFIED RIGHT items. A group sender is moved as an
      * alphanumeric elementary item (IBM, Group moves), so JUSTIFIED
      * applies: right-justified, leftmost characters truncated (NIST
      * NC107A JUST-TEST-04). A group receiver is filled from the left
      * whatever JUSTIFIED members it has. Other senders as controls.
      * IBM's result in each comment.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VJUST1.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  G1.
           05  G1A PIC X(3) VALUE "ABC".
           05  G1N PIC 9(2) VALUE 12.
       01  G2.
           05  G2A PIC X(4) VALUE "WXYZ".
           05  G2B PIC X(9) VALUE "123456789".
       01  J1 PIC X(8) JUSTIFIED RIGHT.
       01  J2 PIC A(4) JUSTIFIED RIGHT.
       01  J3 PIC X(5) JUST.
       01  N1 PIC 9(3) VALUE 45.
       01  T1 VALUE SPACES.
           05  TJ PIC X(6) JUST OCCURS 3.
       01  I1 PIC 9 VALUE 2.
       01  H1 VALUE SPACES.
           05  HJ PIC X(6) JUST.
           05  HX PIC X(4).
       01  X1 PIC X(8).
       PROCEDURE DIVISION.
       P0.
      *    group senders: "   ABC12" "BC12" "ABC12" "23456789"
           MOVE G1 TO J1 DISPLAY 'U01 [' J1 ']'
           MOVE G1 TO J2 DISPLAY 'U02 [' J2 ']'
           MOVE G1 TO J3 DISPLAY 'U03 [' J3 ']'
           MOVE G2 TO J1 DISPLAY 'U04 [' J1 ']'
      *    "       ABC12      " "       ABC12456789"
           MOVE G1 TO TJ (I1) DISPLAY 'U05 [' T1 ']'
           MOVE G2 TO TJ (3) DISPLAY 'U06 [' T1 ']'
      *    a member of a group: " ABC12    "; the group: "ABC12     "
           MOVE G1 TO HJ DISPLAY 'U07 [' H1 ']'
           MOVE G1 TO H1 DISPLAY 'U08 [' H1 ']'
      *    two receivers: "   ABC12" "ABC12   "
           MOVE G1 TO J1 X1 DISPLAY 'U09 [' J1 ']'
           DISPLAY 'U10 [' X1 ']'
      *    controls: "    YZ12" " ABC" "      XY" "     045" "ABABABAB"
           MOVE G2 (3:4) TO J1 DISPLAY 'U11 [' J1 ']'
           MOVE G1A TO J2 DISPLAY 'U12 [' J2 ']'
           MOVE "XY" TO J1 DISPLAY 'U13 [' J1 ']'
           MOVE N1 TO J1 DISPLAY 'U14 [' J1 ']'
           MOVE ALL "AB" TO J1 DISPLAY 'U15 [' J1 ']'
      *    "        " "00000000"
           MOVE SPACES TO J1 DISPLAY 'U16 [' J1 ']'
           MOVE ZERO TO J1 DISPLAY 'U17 [' J1 ']'
           STOP RUN.
