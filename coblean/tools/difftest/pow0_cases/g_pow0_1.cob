       IDENTIFICATION DIVISION.
       PROGRAM-ID. GPOW01.
      * ar2-fix hand case: zero raised to the literal power 0 with ON
      * SIZE ERROR is a size error, and IBM leaves the receiver as it was
      * ("the value of the resultant identifier affected by the size
      * error is not altered"). GnuCOBOL runs ON SIZE ERROR for a zero
      * data base but stores 1 (G-pow00, G01 G03) and folds the literal
      * 0 ** 0 to 1 with no size error (G-litpow00, H02 G02).
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  Z        PIC S9(3)V99 VALUE 0.
       01  R        PIC 9(5)V99 VALUE 0.
       PROCEDURE DIVISION.
       P0.
           MOVE 77 TO R
           COMPUTE R = Z ** 0 ON SIZE ERROR DISPLAY "H01 Z"
               NOT ON SIZE ERROR DISPLAY "H01 N" END-COMPUTE
           DISPLAY "G01 " R
           MOVE 77 TO R
           COMPUTE R = 0 ** 0 ON SIZE ERROR DISPLAY "H02 Z"
               NOT ON SIZE ERROR DISPLAY "H02 N" END-COMPUTE
           DISPLAY "G02 " R
           MOVE 77 TO R
           COMPUTE R = (Z - Z) ** 0 + 5 ON SIZE ERROR DISPLAY "H03 Z"
               NOT ON SIZE ERROR DISPLAY "H03 N" END-COMPUTE
           DISPLAY "G03 " R
           STOP RUN.
