      * STANDARD-2 (and STANDARD-1, NATIVE) with ASCII data: native
      * order (the six IF programs of NIST use it): ORD, CHAR, MAX, MIN,
      * ORD-MAX and ORD-MIN as IBM defines them. Both systems agree.
       IDENTIFICATION DIVISION.
       PROGRAM-ID. VSTD2.
       ENVIRONMENT DIVISION.
       CONFIGURATION SECTION.
       OBJECT-COMPUTER. X
           PROGRAM COLLATING SEQUENCE IS SEQ1.
       SPECIAL-NAMES.
           ALPHABET SEQ1 IS STANDARD-2.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 C1 PIC X VALUE "g".
       01 A3 PIC X(3) VALUE "AbC".
       01 B4 PIC X(4).
       01 N3 PIC 999.
       01 K2 PIC 99 VALUE 66.
       01 T1.
          05 TE PIC 999 OCCURS 3.
       01 D1 PIC S9(3)V9 VALUE -1.5.
       PROCEDURE DIVISION.
           MOVE 37 TO TE(1) MOVE 87 TO TE(2) MOVE 98 TO TE(3).
           COMPUTE N3 = FUNCTION ORD("A") DISPLAY "O1 " N3.
           COMPUTE N3 = FUNCTION ORD(C1) + 1 DISPLAY "O2 " N3.
           COMPUTE N3 = FUNCTION ORD(A3(2:1)) DISPLAY "O3 " N3.
           MOVE FUNCTION CHAR(37) TO C1 DISPLAY "H1 " C1 "|".
           MOVE FUNCTION CHAR(K2) TO C1 DISPLAY "H2 " C1 "|".
           MOVE FUNCTION CHAR(TE(2)) TO C1 DISPLAY "H3 " C1 "|".
           IF FUNCTION CHAR(TE(3)) = "a" DISPLAY "H4 Y" ELSE
              DISPLAY "H4 N".
           COMPUTE N3 = FUNCTION ORD(FUNCTION CHAR(4)) DISPLAY "H5 " N3.
           MOVE FUNCTION MAX("R" A3 "I" "a") TO B4 DISPLAY "M1 " B4 "|".
           MOVE FUNCTION MIN("R" A3 "I" "a") TO B4 DISPLAY "M2 " B4 "|".
           COMPUTE N3 = FUNCTION ORD-MAX("A" A3 "P") DISPLAY "M3 " N3.
           COMPUTE N3 = FUNCTION ORD-MIN("S" "D" A3) DISPLAY "M4 " N3.
           COMPUTE N3 = FUNCTION ORD-MAX(5, 3, 8, 8, 1)
           DISPLAY "M5 " N3.
           COMPUTE N3 = FUNCTION ORD-MIN(D1, 4, -1.4, -1.5)
           DISPLAY "M6 " N3.
           COMPUTE N3 = FUNCTION ORD-MAX(FUNCTION ORD-MAX(1, 4), 3, 1)
           DISPLAY "M7 " N3.
           COMPUTE N3 = FUNCTION MAX(4, D1, 6.5) * 2 DISPLAY "M8 " N3.
           STOP RUN.
