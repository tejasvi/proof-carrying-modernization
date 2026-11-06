       IDENTIFICATION DIVISION.
       PROGRAM-ID. UPOWLF.
      * ar2-fix hand case: F2 ** 2 (i 28 + d 8 > 30) in a function
      * argument: its dmax places depend on the open reading of the
      * inner dmax (the statement's 6, the argument's 4); unsupported.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  F2       PIC 9(14)V9(4) VALUE 12.5.
       01  S1       PIC S9(3)V99 VALUE 1.5.
       01  R6       PIC 9(12)V9(6) VALUE 0.
       PROCEDURE DIVISION.
       P0.
           COMPUTE R6 = FUNCTION MAX (S1 ** 2, 1)
           DISPLAY "V01 " R6
           COMPUTE R6 = FUNCTION MAX (F2 ** 2, 1)
           DISPLAY "U01 " R6
           STOP RUN.
