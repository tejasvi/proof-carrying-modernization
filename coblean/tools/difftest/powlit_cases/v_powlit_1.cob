       IDENTIFICATION DIVISION.
       PROGRAM-ID. VPOWL1.
      * ar2-fix hand case: powers by a literal exponent whose places IBM
      * carries without a change of the value: exactly (i + d below 30,
      * or 30 with an odd number of digits in the base) or with dmax
      * places that keep every digit the result shows.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  L4       PIC S9(15) VALUE 999999999999999.
       01  S1       PIC S9(3)V99 VALUE 12.25.
       01  F2       PIC 9(14)V9(4) VALUE 12.5.
       01  L1       PIC S9(16) VALUE 123456.
       01  X18      PIC 9(18) VALUE 0.
       01  R4       PIC 9(14)V9(4) VALUE 0.
       01  E4       PIC -(13)9.9(4).
       PROCEDURE DIVISION.
       P0.
      * V01 L4 ** 2: i 30 + d 0 = 30, 15 digits (odd): carried exactly
           COMPUTE X18 = L4 ** 2 / 1000000000000
           DISPLAY "V01 " X18
      * V02 S1 ** 3: 15 digits
           COMPUTE R4 = S1 ** 3
           MOVE R4 TO E4
           DISPLAY "V02 " E4
      * V03 a literal base: 1.5 ** 2
           COMPUTE R4 = 1.5 ** 2 + S1
           MOVE R4 TO E4
           DISPLAY "V03 " E4
      * V04 F2 ** 2: i 28 + d 8 > 30, dmax 4 places, all R4 shows
           COMPUTE R4 = F2 ** 2
           MOVE R4 TO E4
           DISPLAY "V04 " E4
      * V05 L1 ** 2 in a condition: i 32, dmax 0, a value of 11 digits
           IF L1 ** 2 > 15241383935 DISPLAY "V05 Y" ELSE DISPLAY "V05 N"
           END-IF
           STOP RUN.
