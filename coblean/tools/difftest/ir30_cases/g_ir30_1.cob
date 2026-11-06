       IDENTIFICATION DIVISION.
       PROGRAM-ID. GIR301.
      * ar2-fix hand case, G-ir30: IBM cuts the decimal places of an
      * intermediate result of more than 30 digits (rows 3 and 4 of the
      * Programming Guide's table); GnuCOBOL computes exactly.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A9       PIC 9(9)V9(9) VALUE 1.123456789.
       01  B9       PIC 9(9)V9(9) VALUE 1.987654321.
       01  C8       PIC 9(8) VALUE 10000000.
       01  X9       PIC 9(8)V9(9) VALUE 0.
       01  A14      PIC 9(14)V9(4) VALUE 1.1111.
       01  B14      PIC 9(14)V9(4) VALUE 1.1111.
       01  X14      PIC 9(14)V9(4) VALUE 0.
       01  F1       PIC S9(9)V9(9) VALUE 1.123456789.
       01  F3       PIC S9(4)V9(14) VALUE 1.12345678901235.
       01  S2       PIC 99 VALUE 3.
       01  L13      PIC 9(13) VALUE 1000000000000.
       01  R6       PIC S9(12)V9(6) VALUE 0.
       01  E6       PIC -(12)9.9(6).
       PROCEDURE DIVISION.
       P0.
      * G01 row 3: A9 * B9 (i 18 + d 18, dmax 9) carried with 12
      * decimal places, times C8 (the final result)
           COMPUTE X9 = A9 * B9 * C8
           DISPLAY "G01 " X9
      * G02 row 4: A14 * B14 (i 28 + d 8, dmax 4) carried with 4
           COMPUTE X14 = A14 * B14 * 10
           DISPLAY "G02 " X14
      * G03 a condition: A9 * B9 row 3, then times C8 row 4 (9 places),
      * equal to the literal on IBM, greater in exact arithmetic
           IF A9 * B9 * C8 > 22330437.41112 DISPLAY "G03 Y"
           ELSE DISPLAY "G03 N" END-IF
      * G04 F1 * F3 (i 13 + d 23, dmax 14) carried with 17 places, so
      * its quotient by S2 has 17 places ("(d2 - d1) or dmax")
           COMPUTE R6 = (F1 * F3) / S2 * L13
           MOVE R6 TO E6
           DISPLAY "G04 " E6
           STOP RUN.
