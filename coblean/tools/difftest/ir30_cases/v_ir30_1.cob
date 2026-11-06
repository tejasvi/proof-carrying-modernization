       IDENTIFICATION DIVISION.
       PROGRAM-ID. VIR301.
      * ar2-fix hand case: intermediate results over 30 digits whose
      * places IBM carries without a change of the value (row 2
      * checks, final results), and the IF110A, IF133A, NC250A shapes.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  A16      PIC 9(16) VALUE 2.
       01  B16      PIC 9(16) VALUE 3.
       01  X17      PIC 9(17) VALUE 0.
       01  A14      PIC 9(14)V9(4) VALUE 1.1111.
       01  B14      PIC 9(14)V9(4) VALUE 1.1111.
       01  X14      PIC 9(14)V9(4) VALUE 0.
       01  Y14      PIC 9(14)V9(4) VALUE 0.
       01  R10A     PIC S9(10) VALUE 1234567891.
       01  R10D     PIC S9(10) VALUE 98765.
       01  WSNUM    PIC S9(5)V9(6) VALUE 0.
       01  B10      PIC S9(10) VALUE 7.
       01  N1       PIC 9 VALUE 3.
       01  L18A     PIC 9(18) VALUE 123456789.
       01  L18B     PIC 9(18) VALUE 987654321.
       01  L18C     PIC 9(18) VALUE 5.
       01  X18      PIC 9(18) VALUE 0.
       01  S2       PIC 99 VALUE 7.
       01  L18X     PIC 9(18) VALUE 999999999999999999.
       01  E4       PIC -(5)9.9(6).
       PROCEDURE DIVISION.
       P0.
      * V01 A16 * B16 + 1: the product carried with 30 integer places
           COMPUTE X17 = A16 * B16 + 1
           DISPLAY "V01 " X17
      * V02 a condition (every operation an intermediate result)
           IF A16 * B16 > 5 DISPLAY "V02 Y" ELSE DISPLAY "V02 N" END-IF
      * V03 IF133A F-REM-TEST-14
           COMPUTE WSNUM = FUNCTION REM (FUNCTION REM (R10A, R10D),
                                         R10D)
           MOVE WSNUM TO E4
           DISPLAY "V03 " E4
      * V04 MULTIPLY GIVING two receivers (row 4: 4 places kept)
           MULTIPLY A14 BY B14 GIVING X14 Y14
           DISPLAY "V04 " X14 " " Y14
      * V05 IF110A F-FACTORIAL-TEST-07 (the add is the final result)
           COMPUTE WSNUM = FUNCTION FACTORIAL (1) + B10
           MOVE WSNUM TO E4
           DISPLAY "V05 " E4
      * V06 NC250A: a power by a data item plus 1 in a condition
           IF 10 ** N1 + 1 > 1000 DISPLAY "V06 Y" ELSE DISPLAY "V06 N"
           END-IF
      * V07 FUNCTION SUM of 18-digit items (its steps carried)
           COMPUTE X18 = FUNCTION SUM (L18A L18B L18C L18A L18B L18C)
           DISPLAY "V07 " X18
      * V08 a final result of 36 digits (MULTIPLY GIVING, one receiver)
           MULTIPLY L18A BY L18B GIVING X18
           DISPLAY "V08 " X18
      * V09 a quotient of a 36-digit product (row 2 check)
           COMPUTE X18 = (L18A * L18B) / S2
           DISPLAY "V09 " X18
      * V10 a final result of 36 digits stored by the truncation rules
      * (no ON SIZE ERROR): no intermediate result, no 30-digit cut
           MULTIPLY L18X BY L18X GIVING X18
           DISPLAY "V10 " X18
           STOP RUN.
