      * An ALPHABET of literals and figurative constants: SPACE
      * shares a position with Z (padding spaces compare equal to Z);
      * MAX keeps the leftmost of equal arguments; INSPECT matches
      * characters, not positions. Both systems agree on every line.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VCOLL1.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS "Z" ALSO SPACE "Q" ALSO QUOTE ALSO ZERO
              "M"
           ALPHABET SEQ2 IS 91 THRU 88 50 ALSO 66.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 H PIC X VALUE HIGH-VALUE.
       01 L PIC X VALUE LOW-VALUE.
       01 C1 PIC X.
       01 C2 PIC X.
       01 A3 PIC X(3).
       01 B3 PIC X(3).
       01 K2 PIC 99.
       PROCEDURE DIVISION.
           DISPLAY "H=" H "|L=" L "|".
           MOVE "Z" TO C1 MOVE " " TO C2
           IF C1 = C2 DISPLAY "F01 Y" ELSE DISPLAY "F01 N".
           MOVE "Q" TO C1 MOVE QUOTE TO C2
           IF C1 = C2 DISPLAY "F02 Y" ELSE DISPLAY "F02 N".
           MOVE "0" TO C2
           IF C1 = C2 DISPLAY "F03 Y" ELSE DISPLAY "F03 N".
           MOVE "M" TO C1 MOVE "A" TO C2
           IF C1 < C2 DISPLAY "F04 Y" ELSE DISPLAY "F04 N".
           MOVE "Z" TO A3 MOVE "ZZZ" TO B3
           IF A3 = B3 DISPLAY "F05 Y" ELSE DISPLAY "F05 N".
           MOVE "AB" TO A3 MOVE "ABZ" TO B3
           IF A3 = B3 DISPLAY "F06 Y" ELSE DISPLAY "F06 N".
           MOVE FUNCTION MAX(A3 B3) TO C1 DISPLAY "F07 " C1 "|".
           COMPUTE K2 = FUNCTION ORD-MAX(A3 B3) DISPLAY "F08 " K2.
           MOVE "M" TO C1
           IF C1 < SPACE DISPLAY "F09 Y" ELSE DISPLAY "F09 N".
           IF C1 > ZERO DISPLAY "F10 Y" ELSE DISPLAY "F10 N".
           MOVE "Q" TO A3
           MOVE 0 TO K2 INSPECT A3 TALLYING K2 FOR ALL SPACE
           DISPLAY "F11 " K2.
           IF H > C1 DISPLAY "F12 Y" ELSE DISPLAY "F12 N".
           IF L < C1 DISPLAY "F13 Y" ELSE DISPLAY "F13 N".
           STOP RUN.
