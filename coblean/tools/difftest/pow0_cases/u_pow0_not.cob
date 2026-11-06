       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOW0N.
      * ar2-fix hand case: a power by the literal exponent 0 in a COMPUTE
      * with NOT ON SIZE ERROR and no ON SIZE ERROR. A nonzero base: 1,
      * and the phrase runs. A zero base: the size error skips the phrase
      * while the value 1 is stored, which the model does not represent:
      * unsupported (U01 the step not reached).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  Z        PIC S9(3)V99 VALUE 0.
       01  N        PIC S9(3)V99 VALUE -2.5.
       01  R        PIC 9(5)V99 VALUE 0.
       PROCEDURE DIVISION.
       P0.
           MOVE 77 TO R
           COMPUTE R = N ** 0 NOT ON SIZE ERROR ADD 4 TO R
           END-COMPUTE
           DISPLAY "V01 " R
           MOVE 77 TO R
           COMPUTE R = Z ** 0 NOT ON SIZE ERROR ADD 4 TO R
           END-COMPUTE
           DISPLAY "U01 " R
           STOP RUN.
