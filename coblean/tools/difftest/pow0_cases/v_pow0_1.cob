       IDENTIFICATION DIVISION.
       PROGRAM-ID. VPOW01.
      * ar2-fix hand case: powers by the literal exponent 0 whose value
      * is 1: nonzero bases, and a zero base without ON SIZE ERROR (IBM:
      * "The value returned is 1, and a message is issued").
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  Z        PIC S9(3)V99 VALUE 0.
       01  N        PIC S9(3)V99 VALUE -2.5.
       01  R        PIC 9(5)V99 VALUE 0.
       PROCEDURE DIVISION.
       P0.
      * V01 a nonzero item base with ON SIZE ERROR
           MOVE 77 TO R
           COMPUTE R = N ** 0 ON SIZE ERROR DISPLAY "V01 Z"
               NOT ON SIZE ERROR DISPLAY "V01 N" END-COMPUTE
           DISPLAY "V01 " R
      * V02 a zero base without ON SIZE ERROR: 1
           MOVE 77 TO R
           COMPUTE R = Z ** 0
           DISPLAY "V02 " R
      * V03 the literals 7 and 1.5 as bases
           COMPUTE R = 7 ** 0 + 1.5 ** 0 ON SIZE ERROR DISPLAY "V03 Z"
               NOT ON SIZE ERROR DISPLAY "V03 N" END-COMPUTE
           DISPLAY "V03 " R
      * V04 an expression base, times 3
           COMPUTE R = (N * 2) ** 0 * 3
           DISPLAY "V04 " R
      * V05 a zero base in a condition: 1
           IF Z ** 0 = 1 DISPLAY "V05 Y" ELSE DISPLAY "V05 N" END-IF
      * V06 the literal 0 as the base without ON SIZE ERROR: 1
           MOVE 77 TO R
           COMPUTE R = 0 ** 0 + 4
           DISPLAY "V06 " R
           STOP RUN.
