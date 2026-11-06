       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPOWL1.
      * ar2-fix hand case, G-powlit: a power by a literal exponent with
      * i + d over 30 (or 30 and an even number of digits in the base)
      * is held with dmax decimal places as for an integral data-name
      * exponent; GnuCOBOL computes it exactly. G04, G-litpow64:
      * GnuCOBOL folds an integer literal ** literal in 64-bit binary.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  F2       PIC 9(14)V9(4) VALUE 1.2345.
       01  P10      PIC 9(6)V9(4) VALUE 1.2345.
       01  X18      PIC 9(18) VALUE 0.
       01  R4       PIC 9(14)V9(4) VALUE 0.
       01  R6       PIC 9(12)V9(6) VALUE 0.
       01  E4       PIC -(13)9.9(4).
       01  E6       PIC -(11)9.9(6).
       PROCEDURE DIVISION.
       P0.
      * G01 F2 ** 2: i 28 + d 8 > 30: 4 places (dmax), then times 10
           COMPUTE R4 = F2 ** 2 * 10
           MOVE R4 TO E4
           DISPLAY "G01 " E4
      * G02 1.5 ** 40: 8 integer + 40 decimal places: 6 places (dmax)
           COMPUTE R6 = 1.5 ** 40 * 1000
           MOVE R6 TO E6
           DISPLAY "G02 " E6
      * G03 P10 ** 3: i 18 + d 12 = 30, 10 digits (even): 4 places
           COMPUTE R4 = P10 ** 3 * 1000
           MOVE R4 TO E4
           DISPLAY "G03 " E4
      * G04 2 ** 64: 20 integer digits, carried exactly (GnuCOBOL: 0)
           COMPUTE X18 = 2 ** 64 / 1000
           DISPLAY "G04 " X18
           STOP RUN.
